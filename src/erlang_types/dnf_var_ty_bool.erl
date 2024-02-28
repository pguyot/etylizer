-module(dnf_var_ty_bool).

-define(ELEMENT, ty_variable).
-define(TERMINAL, bdd_bool).

-export([is_empty/1,normalize/3, substitute/4]).
-export([var/1, bool/1, all_variables/1, transform/2, apply_to_node/3]).

-include("bdd_var.hrl").

% fully generic
bool(Ty) -> terminal(Ty).
var(Var) -> node(Var).

% partially generic
is_empty_coclause(_Pos, _Neg, T) -> bdd_bool:is_empty(T).
is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
normalize(Ty, Fixed, M) -> 
  error({todo, Ty}).
  % dnf(Ty, {
  %   fun(Pos, Neg, DnfTy) -> normalize_coclause(Pos, Neg, DnfTy, Fixed, M) end,
  %   fun constraint_set:meet/2
  % }).

% module specific implementations
normalize_coclause(PVar, NVar, Ty, Fixed, M) ->
  case ty_rec:empty() of
    Ty -> [[]];
    _ ->
      case ty_ref:is_normalized_memoized(Ty, Fixed, M) of
        true ->
          % TODO test case
          error({todo, extract_test_case, memoize_function}); %[[]];
        miss ->
          error(todo)
          % memoize only non-variable component t0
          % ty_rec:normalize(Ty, PVar, NVar, Fixed, sets:union(M, sets:from_list([List])))
      end
  end.



% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  error(todo),
  dnf_ty_list:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_list:substitute(N, Subst, M) end).
