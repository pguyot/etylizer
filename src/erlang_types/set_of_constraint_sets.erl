-module(set_of_constraint_sets).

%% API
-export([print/1, is_valid_substitution/2, is_smaller/2, is_equivalent/3]).

%
is_smaller([], _S2) -> true;
is_smaller([C | Cs], S2) ->
  constraint_set:has_smaller_constraint(C, S2)
  andalso is_smaller(Cs, S2).

is_equivalent(_, _, []) -> true;
is_equivalent(S1, S2, [O | Os]) ->
  Result =
    case has_valid_substitution(S1, O) of
      true -> has_valid_substitution(S2, O);
      false -> not has_valid_substitution(S2, O)
    end,

  Result andalso is_equivalent(S1, S2, Os).

has_valid_substitution([], _Substitution) -> false;
has_valid_substitution([Cs | Css], Substitution) ->
  is_valid_substitution(Cs, Substitution)
  orelse has_valid_substitution(Css, Substitution).


is_valid_substitution([], _) -> true;
is_valid_substitution([{Var, Left, Right} | Cs], Substitution) ->
  SubstitutedTyVar = ty_rec:substitute(ty_rec:variable(Var), Substitution),
  SubstitutedLeft = ty_rec:substitute(Left, Substitution),
  SubstitutedRight = ty_rec:substitute(Right, Substitution),

  ty_rec:is_subtype(SubstitutedLeft, SubstitutedTyVar) andalso
    ty_rec:is_subtype(SubstitutedTyVar, SubstitutedRight) andalso
    is_valid_substitution(Cs, Substitution).

print([]) -> "";
print([{Left, Right} | Rest]) -> 
  io_lib:format("~s <: ~s~n~s", [ty_rec:print(Left), ty_rec:print(Right), print(Rest)]).