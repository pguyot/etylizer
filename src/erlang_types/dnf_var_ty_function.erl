-module(dnf_var_ty_function).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_function).
-define(F(Z), fun() -> Z end).


-export([is_empty/1]).
-export([normalize/4, substitute/4]).
-export([var/1, function/1, all_variables/2, mall_variables/2, transform/2]).

-include("bdd_var.hrl").

function(Tuple) -> terminal(Tuple).
var(Var) -> node(Var).

mall_variables({Default, Others}, M) when is_map(Others) ->
  lists:usort(lists:flatten(
    all_variables(Default, M) ++
    lists:map(fun({_K,V}) -> all_variables(V, M) end, maps:to_list(Others))
  ));
mall_variables(Ty, M) -> all_variables(Ty, M).

is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_function:is_empty(T).

normalize(Size, Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, DnfTy) -> normalize_coclause(Size, Pos, Neg, DnfTy, Fixed, M) end,
  fun constraint_set:meet/2
}).

normalize_coclause(Size, PVar, NVar, Function, Fixed, M) ->
  case dnf_ty_function:empty() of
    Function -> [[]];
    _ ->
      case ty_ref:is_normalized_memoized({PVar, NVar, Function}, Fixed, M) of
        true ->
          [[]];
        miss ->
          dnf_ty_function:normalize(Size, Function, PVar, NVar, Fixed, sets:union(M, sets:from_list([{PVar, NVar, Function}])))
      end
  end.


% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_function:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_function:substitute(N, Subst, M) end).
