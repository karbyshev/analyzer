(* 
 * Copyright (c) 2005-2007,
 *     * University of Tartu
 *     * Vesal Vojdani <vesal.vojdani@gmail.com>
 *     * Kalmer Apinis <kalmera@ut.ee>
 *     * Jaak Randmets <jaak.ra@gmail.com>
 *     * Toomas Römer <toomasr@gmail.com>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 * 
 *     * Redistributions of source code must retain the above copyright notice,
 *       this list of conditions and the following disclaimer.
 * 
 *     * Redistributions in binary form must reproduce the above copyright notice,
 *       this list of conditions and the following disclaimer in the documentation
 *       and/or other materials provided with the distribution.
 * 
 *     * Neither the name of the University of Tartu nor the names of its
 *       contributors may be used to endorse or promote products derived from
 *       this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)

open Pretty

module type S = 
sig
  include Lattice.S
  type elt
  val empty: unit -> t
  val is_empty: t -> bool
  val mem: elt -> t -> bool
  val add: elt -> t -> t
  val singleton: elt -> t
  val remove: elt -> t -> t
  val union: t -> t -> t
  val inter: t -> t -> t
  val diff: t -> t -> t
  val subset: t -> t -> bool
  val iter: (elt -> unit) -> t -> unit
  val map: (elt -> elt) -> t -> t
  val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all: (elt -> bool) -> t -> bool
  val exists: (elt -> bool) -> t -> bool
  val filter: (elt -> bool) -> t -> t
  val partition: (elt -> bool) -> t -> t * t
  val cardinal: t -> int
  val elements: t -> elt list
  val min_elt: t -> elt
  val max_elt: t -> elt
  val choose: t -> elt
  val split: elt -> t -> t * bool * t
end

exception Unsupported of string

module Blank = 
struct
  let empty _ = raise (Unsupported "empty")
  let is_empty _ = raise (Unsupported "is_empty") 
  let mem _ _ = raise (Unsupported "mem") 
  let add _ _ = raise (Unsupported "add") 
  let singleton _ = raise (Unsupported "singleton") 
  let remove _ _ = raise (Unsupported "remove") 
  let union _ _ = raise (Unsupported "union") 
  let inter _ _ = raise (Unsupported "inter") 
  let diff _ _ = raise (Unsupported "diff") 
  let subset _ _ = raise (Unsupported "subset") 
  let iter _ _ = raise (Unsupported "iter") 
  let map _ _ = raise (Unsupported "map") 
  let fold _ _ _ = raise (Unsupported "fold") 
  let for_all _ _ = raise (Unsupported "for_all") 
  let exists _ _ = raise (Unsupported "exists") 
  let filter _ _ = raise (Unsupported "filter") 
  let partition _ _ = raise (Unsupported "partition") 
  let cardinal _ = raise (Unsupported "cardinal") 
  let elements _ = raise (Unsupported "elements") 
  let min_elt _ = raise (Unsupported "min_elt") 
  let max_elt _ = raise (Unsupported "max_elt") 
  let choose _ = raise (Unsupported "choose") 
  let split _ _ = raise (Unsupported "split") 
end

module Make (Base: Printable.S) = 
struct
  include Set.Make(Base)
  include Printable.Blank
  include Lattice.StdCousot
  let empty _ = empty
  let leq  = subset
  let join = union
  let meet = inter
  let bot = empty
  let is_bot = is_empty
  let top () = raise (Lattice.Unsupported "Set has no top")
  let is_top _ = false

  let map f s = 
    let add_to_it x s = add (f x) s in
      fold add_to_it s (empty ())
      
  let pretty_f _ () x = 
    let elts = elements x in
    let content = List.map (Base.pretty ()) elts in
    let rec separate x =
      match x with
        | [] -> []
        | [x] -> [x]
        | (x::xs) -> x ++ (text ", ") :: separate xs
    in 
    let separated = separate content in
    let content = List.fold_left (++) nil separated in
      (text "{") ++ content ++ (text "}")
	
  (** Short summary for sets. *)
  let short w x : string = 
    let usable_length = w - 5 in
    let all_elems : string list = List.map (Base.short usable_length) (elements x) in
      Printable.get_short_list "{" "}" usable_length all_elems 
      

  let toXML_f sf x = 
    let esc = Goblintutil.escape in
    let elems = List.map Base.toXML (elements x) in
      Xml.Element ("Node", [("text", esc (sf max_int x))], elems)

  let toXML s  = toXML_f short s
  let pretty () x = pretty_f short () x

  let isSimple x = 
    (List.length (elements x)) < 3
end

module SensitiveConf (C: Printable.ProdConfiguration) (Base: Lattice.S) (User: Printable.S) = 
struct
  module Elt = Printable.ProdConf (C) (Base) (User)
  include Make(Elt)

  let leq s1 s2 = 
    (* I want to check that forall e in x, the same key is in y with it's base
     * domain element being leq of this one *)
    let p (b1,u1) = exists (fun (b2,u2) -> User.equal u1 u2 && Base.leq b1 b2) s2 in
      for_all p s1

  let join s1 s2 = 
    (* Ok, so for each element (b2,u2) in s2, we check in s1 for elements that have
     * equal user values (there should be at most 1) and we either join with it, or
     * just add the element to our accumulator res and remove it from s1 *)
    let f (b2,u2) (s1,res) = 
      let (s1_match, s1_rest) = partition (fun (b1,u1) -> User.equal u1 u2) s1 in
      let el = 
        try let (b1,u1) = choose s1_match in (Base.join b1 b2, u2)
        with Not_found -> (b2,u2)
      in
        (s1_rest, add el res)
    in
    let (s1', res) = fold f s2 (s1, empty ()) in
      union s1' res

  let add e s = join (singleton e) s

  (* The meet operation is slightly different from the above, I think this is
   * the right thing, the intuition is from thinking of this as a MapBot *)
  let meet s1 s2 = 
    let f (b2,u2) (s1,res) = 
      let (s1_match, s1_rest) = partition (fun (b1,u1) -> User.equal u1 u2) s1 in
      let res =
        try 
          let (b1,u1) = choose s1_match in 
            add (Base.meet b1 b2, u2) res
        with Not_found -> res
      in
        (s1_rest, res)
    in
      snd (fold f s2 (s1, empty ()))
end

module Sensitive = SensitiveConf (struct
                                    let expand_fst = true
                                    let expand_snd = true
                                  end)

module type ToppedSetNames = 
sig
  val topname: string
end

module ToppedSet (Base: Printable.S) (N: ToppedSetNames) =
struct 
  module S = Make (Base) 
  include Printable.Blank
  include Lattice.StdCousot
  type t = All | Set of S.t
  type elt = Base.t

  let empty () = Set (S.empty ())
  let is_empty x = 
    match x with
      | All -> false 
      | Set x -> S.is_empty x
  let mem x s = 
    match s with
      | All -> true
      | Set s -> S.mem x s
  let add x s = 
    match s with
      | All -> All
      | Set s -> Set (S.add x s)
  let singleton x = Set (S.singleton x)
  let remove x s = 
    match s with 
      | All -> All   (* NB! NB! NB! *)
      | Set s -> Set (S.remove x s)
  let union x y = 
    match x, y with
      | All, _ -> All
      | _, All -> All
      | Set x, Set y -> Set (S.union x y)
  let inter x y = 
    match x, y with
      | All, y -> y
      | x, All -> x
      | Set x, Set y -> Set (S.inter x y)
  let diff x y = 
    match x, y with
      | x, All -> empty ()
      | All, y -> All (* NB! NB! NB! *)
      | Set x, Set y -> Set (S.diff x y)
  let subset x y =
    match x, y with
      | _, All -> true
      | All, _ -> false
      | Set x, Set y -> S.subset x y  

  let schema normal abnormal x = 
    match x with
      | All -> raise (Unsupported abnormal)
      | Set t -> normal t
  (* HACK! Map is an exception in that it doesn't throw an exception! *)
  let map f x =
    match x with
      | All -> All
      | Set t -> Set (S.map f t)

  let iter f = schema (S.iter f) "iter on All"
(*  let map f = schema (fun t -> Set (S.map f t)) "map"*)
  let fold f x e = schema (fun t -> S.fold f t e) "fold on All" x
  let for_all f = schema (S.for_all f) "for_all on All"
  let exists f = schema (S.exists f) "exists on All"
  let filter f = schema (fun t -> Set (S.filter f t)) "filter on All"
  let elements = schema S.elements "elements on All"
  let cardinal = schema S.cardinal "cardinal on All"
  let min_elt = schema S.min_elt "min_elt on All"
  let max_elt = schema S.max_elt "max_elt on All"
  let choose = schema S.choose "choose on All"
  let partition f = schema (fun t -> match S.partition f t 
                            with (a,b) -> (Set a, Set b)) "filter on All"
  let split e = schema (fun t -> match S.split e t 
                        with (a,tv,b) -> (Set a,tv,Set b)) "split on All"


  (* The printable implementation *)

  let pretty_f _ () x = 
    match x with 
      | All -> text N.topname
      | Set t -> S.pretty () t

  let short w x : string = 
    match x with 
      | All -> N.topname
      | Set t -> S.short w t

  let isSimple x = 
    match x with 
      | All -> true
      | Set t -> S.isSimple t

  let toXML_f _ x = 
    match x with
      | All -> Xml.Element ("Leaf", [("text", N.topname)], [])
      | Set t -> S.toXML t

  let pretty () x = pretty_f short () x
  let toXML x = toXML_f short x


  (* Lattice implementation *)

  let bot = empty
  let is_bot = is_empty
  let top () = All
  let is_top x = x = All

  let leq = subset
  let join = union
  let meet = inter
end

(* This one just removes the extra "{" notation and also by always returning
 * false for the isSimple, the answer looks better, but this is essentially a
 * hack. All the pretty printing needs some rethinking. *)
module HeadlessSet (Base: Printable.S) = 
struct
  include Make(Base)

  let isSimple _ = false

  let pretty_f _ () x = 
    let elts = elements x in
    let content = List.map (Base.pretty ()) elts in
    let rec separate x =
      match x with
        | [] -> []
        | [x] -> [x]
        | (x::xs) -> x ++ (text ", ") ++ line :: separate xs
    in 
    let separated = separate content in
    let content = List.fold_left (++) nil separated in
      content 

  let pretty () x = pretty_f short () x
end