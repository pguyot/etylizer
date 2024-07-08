-module(dnf_var_ty_atom).

-define(P, {ty_atom, ty_variable}).
-define(ELEMENT, ty_variable).
-define(TERMINAL, ty_atom).

-export([to_line/1, apply_to_node/3]).
-export([is_empty/1, normalize/3, substitute/4]).
-export([var/1, ty_atom/1, all_variables/2]).
-export([transform/2]).

-export_type([type/0]).
-type type() :: term(). %TODO

-include("bdd_var.hrl").

to_line(DnfVar) ->
  dnf(DnfVar, {
    fun
      (P,N,T) ->
        {Pos, Neg} = ?TERMINAL:to_line(T),
        P2 = [?ELEMENT:to_line(V) || V <- P],
        P3 = [?ELEMENT:to_line(V) || V <- N],
        [{P2, P3, Pos, Neg}]
    end,
    fun(F1, F2) -> F1 ++ F2 end
  }).

ty_atom(Atom) -> terminal(Atom).
var(Var) -> node(Var).

% partially generic
is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).

is_empty_coclause(_Pos, _Neg, T) -> ty_atom:is_empty(T).

normalize(Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, Atom) -> ty_atom:normalize(Atom, Pos, Neg, Fixed, M) end,
  fun constraint_set:meet/2
}).

% not recursive, no op substitution
apply_to_node(Node, _StdMap, _Memo) ->
  Node.
