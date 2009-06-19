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

(** Abstract domains representing sets. *)

module type S = 
sig
  include Lattice.S
  type elt
  val empty: unit -> t
  (* The empty set. Note that the type is different from standard!  *)
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
  (* A simple map function for functions of type [elt -> elt]. This is
   * non-standard. *)
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
(** A set domain must support all the standard library set operations, which
  * thanks to ocaml's inflexible module system have been copy-pasted. *)

module Make (Base: Printable.S): S with type elt = Base.t
(** A functor for creating a simple set domain, there is no top element, and
  * calling [top ()] will raise an exception *)

module Sensitive (Base: Lattice.S) (User: Printable.S): S with type elt = Base.t * User.t
(** A functor for creating a path sensitive set domain, that joins the base
  * analysis whenever the user elements coincide. Just as above there is no top
  * element, and calling [top ()] will raise an exception *)

module SensitiveConf (C: Printable.ProdConfiguration) (Base: Lattice.S) (User: Printable.S): S with type elt = Base.t * User.t
(** Same as [Sensitive] but with product expansion configuration
  *)

exception Unsupported of string
(* Exception raised when the set domain can not support the requested operation.
 * This will be raised, when trying to iterate a set that has been set to Top *)

module type ToppedSetNames = 
sig
  val topname: string
end
(** Auxiliary signature for naming the top element *)

module ToppedSet (Base: Printable.S) (N: ToppedSetNames): S with type elt = Base.t
(** Functor for creating artificially topped set domains. *)

module HeadlessSet (Base: Printable.S): S with type elt = Base.t