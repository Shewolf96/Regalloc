open Xi_lib
open Xi_lib.Measure
open Ir

let logf fmt = Logger.make_logf __MODULE__ fmt

module Make(Toolbox:Iface.COMPILER_TOOLBOX) = struct

  module Implementation(M:sig
    val cfg: ControlFlowGraph.t
    val proc: procedure
    end) = struct

    open M

    module Coalescencing = Toolbox.RegisterCoalescing

    (* Dostępne rejestry *)
    let available_registers = Toolbox.RegistersDescription.available_registers |> List.sort compare

    (* Liczba dostępnych kolorów *)
    let number_of_available_registers = List.length available_registers

    (* ------------------------------------------------------------------------
     *  Hashtablice z kolorami 
     *)

    (* wstępnie pokolorowane wierzchołki *)
    let base_register2color_assignment : (reg, int) Hashtbl.t = Hashtbl.create 13

    (* kolory wierzchołków *)
    let register2color_assignment : (reg, int) Hashtbl.t = Hashtbl.create 13

    (* pomocnicza tablica -- odwzorowuje kolor na rejestr sprzętowy *)
    let color2register_assignment : (int, reg) Hashtbl.t = Hashtbl.create 13

    (* ------------------------------------------------------------------------
     *  Wstępne kolorowanie
     *)

    let initialize_colors () =
      let color i hard =
        Hashtbl.replace color2register_assignment i hard;
        Hashtbl.replace base_register2color_assignment hard i;
      in
      List.iteri color available_registers

    (* ------------------------------------------------------------------------
     *  Budowanie grafu interferencji 
     *)

    let build_infg () =
      logf "building interference graph";
      let lva = Toolbox.LiveVariablesAnalysis.analyse cfg in
      Logger.extra_debug begin fun () -> 
        Logger.dump_live_variables "before-inf-build" cfg lva;
      end;
      let infg = Toolbox.InterferenceGraphAnalysis.analyse cfg lva in
      Logger.extra_debug begin fun () ->
        Logger.dump_interference_graph "before-simplify" infg
      end;
      infg

    (* ------------------------------------------------------------------------
     *  Pomocnicze funkcje
     *)

    let loop name f = 
      let rec iter i = 
        logf "Starting iteration %s %u" name i;
        let r, should_restart = measure "iteration" f in
        if should_restart then
          iter (succ i)
        else
          r
      in
      iter 0

    (* ------------------------------------------------------------------------
     *  Spilling
     *)

    let compute_spill_costs infg =
      Logger.extra_debug begin fun () ->
        logf "Computing dominators"
      end;
      let dom = Toolbox.DominatorsAnalysis.analyse cfg in
      Logger.extra_debug begin fun () ->
        logf "Computing natural-loops"
      end;
      let nloops = Toolbox.NaturalLoopsAnalysis.analyse cfg dom in
      Logger.extra_debug begin fun () ->
        logf "Computing spill-costs"
      end;
      let spill_costs = Toolbox.SpillCostsAnalysis.analyse cfg nloops in
      Logger.extra_debug begin fun () ->
          Logger.dump_spill_costs spill_costs;
      end;
      spill_costs

    let spill actual_spills = 
      measure "spill" (fun () -> Toolbox.Spilling.spill proc actual_spills);
      actual_spills <> []

    (* ------------------------------------------------------------------------
     * Faza simplify
     *)


    let rec simplify infg num_of_reg stack spill_costs = 
      let get_cost v = match v with
        | REG_Hard _
        | REG_Spec _-> max_int
        | REG_Tmp i -> RegGraph.out_degree infg v
      in
      let min_out_deg vertex acc = match Some vertex, acc with
        | v, None -> v
        | None, v -> v
        | Some v1, Some v2 -> 
          if get_cost v2 < get_cost v1 then Some v2 else Some v1
      in
      let get_spill_cost v = match v with
        | REG_Hard _
        | REG_Spec _-> max_float
        | REG_Tmp i -> 
          let x = float_of_int @@ RegGraph.out_degree infg v in
          let y = float_of_int @@ Hashtbl.find spill_costs v in
          y /. x
      in
      let min_cost vertex acc = match vertex, acc with
        | v1, Some v2 ->
          if get_spill_cost v1 > get_spill_cost v2 then Some v2 else Some v1
          
        | v, None -> Some v

      in

      match RegGraph.fold_vertex min_out_deg infg None with
        | Some ((REG_Tmp _) as v) -> 
          if RegGraph.out_degree infg v < num_of_reg 
            then
              let new_stack = (v, RegGraph.succ infg v)::stack in
              RegGraph.remove_vertex infg v;
              simplify infg num_of_reg new_stack spill_costs
          else begin match RegGraph.fold_vertex min_cost infg None with
            | Some ((REG_Tmp _) as v) -> 
              let new_stack = (v, RegGraph.succ infg v)::stack in
              RegGraph.remove_vertex infg v;
              simplify infg num_of_reg new_stack spill_costs

            | _ -> stack

          end

        | _ -> stack 

(*     let print_reg reg = match reg with
          | REG_Hard i
          | REG_Spec i ->
            print_endline @@ "hs: " ^ string_of_int i
          | REG_Tmp i ->
            print_endline @@ " tmp: " ^  string_of_int i *)

    (* ------------------------------------------------------------------------
     *  Faza Select
     *)
     

    let rec select infg num_of_reg stack actual_spills = 
      match stack with
      | [] -> actual_spills
      | (v, neighbours)::tail -> 
(*         List.iter print_reg neighbours;
        Hashtbl.iter (fun reg color -> match reg with
          | REG_Hard i
          | REG_Spec i ->
            print_endline @@ string_of_int i ^ " hs " ^ string_of_int color
          | REG_Tmp i ->
            print_endline @@ string_of_int i ^ " " ^ string_of_int color ) register2color_assignment; *)
        let find_color succ = 
          match Hashtbl.find_opt register2color_assignment succ with
          | Some col -> (col, succ)
          | _ -> begin match succ with 
            | REG_Tmp _ -> failwith "internal error" 
            | _ -> begin match Hashtbl.find_opt base_register2color_assignment succ with
              | Some col -> (col, succ)
              | _ -> failwith "internal error"
            end
          end

        in
        (* let succ_reg_col_pair_list = List.map find_color (RegGraph.succ infg v) in *)
        let succ_reg_col_pair_list = List.map find_color neighbours in
        (* let succ_reg_col_pair_list = RegGraph.fold_vertex add_pair infg [] in *)
        let succ_reg_col_pair_list = List.sort (fun p1 p2 -> compare p1 p2) succ_reg_col_pair_list in

        let rec select_color i = function
        | [] -> i
        | (col, _)::tail -> if i < col then i else select_color (col+1) tail
        in

        let color = select_color 0 succ_reg_col_pair_list in
        Hashtbl.add register2color_assignment v color;
        if color > number_of_available_registers then 
          select infg num_of_reg tail @@ v::actual_spills
        else select infg num_of_reg tail actual_spills




    (* ------------------------------------------------------------------------
     *  Pętla build-coalesce
     *)

    let build_coalescence () =
      let infg = measure "build" (fun () -> build_infg ()) in
      let changed = measure "coalescence" (fun () ->  Coalescencing.coalesce proc infg available_registers) in
      infg, changed

    let build_coalescence_loop () = 
      loop "build-coalescence" build_coalescence

    (* ------------------------------------------------------------------------
     *  Pętla build-coalesce
     *)

    let single_pass () =
      let init () = begin
          (* resetujemy robocze tablice *)
          Hashtbl.reset register2color_assignment;
          Hashtbl.replace_seq register2color_assignment @@ Hashtbl.to_seq base_register2color_assignment;
      end in
      Logger.extra_debug begin fun () ->
        Logger.dump_ir_proc "begin-loop" proc
      end;
      let init = measure "init" init in
      let infg = measure "build-coalescence " build_coalescence_loop in
      let spill_costs = measure "spillcosts" (fun () -> compute_spill_costs infg) in
      (* uruchom fazę simplify/select/spill *)
      let stack = simplify infg number_of_available_registers [] spill_costs in
      let actual_spills = select infg number_of_available_registers stack [] in

      (* unit na potrzeby interfejsu pomocniczej funkcji loop *)
      (), spill actual_spills

    (* ------------------------------------------------------------------------
     *  Budowanie mapowania rejestrów
     *)

    let build_register_assignment () =
      let register_assignment : (reg, reg) Hashtbl.t = Hashtbl.create 513 in 
      Hashtbl.iter (fun reg col -> Hashtbl.add register_assignment reg (REG_Hard (col+1))) register2color_assignment;
      (* Hashtbl.iter (fun reg col -> Hashtbl.add register_assignment reg ((Hashtbl.find color2register_assignment col))) register2color_assignment; *)

      (* Przejdz tablice register2color_assignment i uzupełnij prawidłowo
       * tablicę register_assignment *)
      register_assignment

    (* ------------------------------------------------------------------------
     *  Main
     *)

    let regalloc () =
      logf "Starting register-allocation";
      initialize_colors ();
      loop "main-loop" single_pass;
      build_register_assignment ()

  end

  let regalloc proc = 
    let module Instance = Implementation(struct
      let cfg = cfg_of_procedure proc
      let proc = proc
      let available_registers = Toolbox.RegistersDescription.available_registers
      end)
    in
    Instance.regalloc ()

end
