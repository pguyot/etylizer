-module(dnf_var).

-define(ELEMENT, ty_variable).
-define(TERMINAL, bdd_bool).

-export([is_empty/1, normalize/3, substitute/4]).
-export([var/1, all_variables/2, transform/2, apply_to_node/3]).

-export_type([type/0]).
-type type() :: term(). %TODO

-include("bdd_var.hrl").

print_ty(Dnf) -> error(todoa).

var(Var) -> node(Var).

% partially generic
is_empty(TyBDD) -> dnf( TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> ?TERMINAL:is_empty(T).

normalize(Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, Atom) -> ?TERMINAL:normalize(Atom, Pos, Neg, Fixed, M) end,
  fun constraint_set:meet/2
}).

% not recursive, no op substitution
apply_to_node(Node, _StdMap, _Memo) ->
  Node.
