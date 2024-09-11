-module(dnf_var_ty_tuple).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_tuple).
-define(F(Z), fun() -> Z end).

-export([normalize/4, substitute/4]).
-export([var/1, tuple/1, all_variables/2, mall_variables/2, transform/2, is_empty/2, apply_to_node/3]).

-export_type([type/0]).
-type type() :: term(). %TODO

% implementations provided by bdd_var.hrl
-include("bdd_var.hrl").

tuple(Tuple) -> terminal(Tuple).
var(Var) -> node(Var).

is_empty(TyBDD, Memo) -> 
  error(todo_tuple_emptyness),
  dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_tuple:is_empty(T).

mall_variables({Default, Others}, Memo) when is_map(Others) ->
  lists:usort(lists:flatten(
    dnf_var:all_variables(Default, Memo) ++
    lists:map(fun({_K,V}) -> all_variables(V, Memo) end, maps:to_list(Others))
  ));
mall_variables(Ty, Memo) -> all_variables(Ty, Memo).

normalize(Size, Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, DnfTy) -> normalize_coclause(Size, Pos, Neg, DnfTy, Fixed, M) end,
  fun constraint_set:meet/2
}).

normalize_coclause(Size, PVar, NVar, Tuple, Fixed, M) ->
  case dnf_ty_tuple:empty() of
    Tuple -> [[]];
    _ ->
      case ty_ref:is_normalized_memoized(Tuple, Fixed, M) of
        true ->
          % TODO test case
          error({todo, extract_test_case, memoize_tuple}); %[[]];
        miss ->
          % memoize only non-variable component t0
          dnf_ty_tuple:normalize(Size, Tuple, PVar, NVar, Fixed, sets:union(M, sets:from_list([Tuple])))
      end
  end.

% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_tuple:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_tuple:substitute(N, Subst, M) end).