(** Flag state values. *)

open Batteries
open Cil
open Pretty
open Analyses
open GobConfig

module Spec =
struct
  include Analyses.DefaultSpec

  let name = "Flag Modes"
  module Dom  = FlagModeDomain.Dom
  module Glob = Glob.Make (Lattice.Unit)
  
  type glob_fun = Glob.Var.t -> Glob.Val.t

  let flag_list = ref []
  
  let init () = flag_list := List.map Json.string @@ get_list "ana.osek.flags"

  (* transfer functions *)
  let assign ctx (lval:lval) (rval:exp) : Dom.t =
    match lval, constFold false rval with
    | (Var f,NoOffset), Const ex when List.mem f.vname !flag_list ->
        Dom.add f (false,true, Const ex) ctx.local
    | (Var f,NoOffset), _ ->
        Dom.remove f ctx.local
    | _ -> ctx.local
   
  let branch ctx (exp:exp) (tv:bool) : Dom.t = 
    match constFold false exp with
      | Lval (Var f, NoOffset) when List.mem f.vname !flag_list  -> 
          Dom.add f (true,not tv,zero) ctx.local
      | BinOp(Ne,Const ex,Lval (Var f, NoOffset),_) 
      | BinOp(Ne,Lval (Var f, NoOffset), Const ex,_) when List.mem f.vname !flag_list -> 
          Dom.add f (true,not tv, Const ex) ctx.local
      | BinOp(Eq,Const ex,Lval (Var f, NoOffset),_) 
      | BinOp(Eq,Lval (Var f, NoOffset), Const ex,_) when List.mem f.vname !flag_list -> 
          Dom.add f (true,tv,Const ex) ctx.local
      | _ -> ctx.local
  
  let body ctx (f:fundec) : Dom.t = 
    ctx.local

  let return ctx (exp:exp option) (f:fundec) : Dom.t = 
    ctx.local
  
  let enter_func ctx (lval: lval option) (f:varinfo) (args:exp list) : (Dom.t * Dom.t) list =
    [ctx.local,ctx.local]
  
  let leave_func ctx (lval:lval option) fexp (f:varinfo) (args:exp list) (au:Dom.t) : Dom.t =
    au
  
  let special_fn ctx (lval: lval option) (f:varinfo) (arglist:exp list) : (Dom.t * Cil.exp * bool) list =
    [ctx.local,Cil.integer 1, true]

  let startstate v = Dom.top ()
  let otherstate v = Dom.top ()
  let exitstate  v = Dom.top ()
end

let _ = 
  let module Spec2 : Spec2 = Constraints.Spec2OfSpec (Spec) in
  MCP.register_analysis "fmode" (module Spec2 : Spec2)
  
module BaseMCP = 
  MCP.ConvertToMCPPart
        (Spec)
        (struct let name = "fmode" 
                let depends = []
                type lf = Spec.Dom.t
                let inject_l x = `FlagModeDom x
                let extract_l x = match x with `FlagModeDom x -> x | _ -> raise MCP.SpecificationConversionError
                type gf = Spec.Glob.Val.t
                let inject_g x = `None
                let extract_g x = match x with `None -> () | _ -> raise MCP.SpecificationConversionError
         end)
