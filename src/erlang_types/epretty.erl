-module(epretty).

-compile([nowarn_shadow_vars]).

-export([
         parens/1,
         brackets/1,
         braces/1,
         comma/2, comma_sep/1,
         beside/2, beside/3, beside/4,
         sep_by/2,
         render_list/2, render_list/3,
         render/1,
         with_parens/2,
         text/1
        ]).

%-import(prettypr, [text/1]).
-type doc() :: prettypr:document().

text(T) -> prettypr:text(T).

-spec parens(doc()) -> doc().
parens(D) -> beside(text("("), D, text(")")).

-spec brackets(doc()) -> doc().
brackets(D) -> beside(text("{"), D, text("}")).

-spec braces(doc()) -> doc().
braces(D) -> beside(text("["), D, text("]")).

-spec comma(doc(), doc()) -> doc().
comma(D1, D2) -> comma_sep([D1, D2]).

-spec beside(doc(), doc()) -> doc().
beside(D1, D2) ->
    case is_list(D1) of
        false -> prettypr:beside(D1, D2);
        true -> errors:bug("beside called with list argument ~w", [D1])
    end.

-spec beside(doc(), doc(), doc()) -> doc().
beside(D1, D2, D3) -> beside(D1, beside(D2, D3)).

-spec beside(doc(), doc(), doc(), doc()) -> doc().
beside(D1, D2, D3, D4) -> beside(D1, beside(D2, beside(D3, D4))).

-spec comma_sep(list(doc())) -> doc().
comma_sep(L) -> sep_by(text(","), L).

% Automatically appends a space or a newline character to Sep.
-spec sep_by(doc(), list(doc())) -> doc().
sep_by(_Sep, []) -> text("");
sep_by(_Sep, [D]) -> D;
sep_by(Sep, Docs) ->
    WithSep =
        lists:foldr(
          fun(D, Acc) ->
                  case Acc of
                      [] -> [D]; % last without trailing sep
                      _ -> [beside(D, Sep) | Acc]
                  end
          end,
          [],
          Docs),
    Res = prettypr:sep(WithSep),
    Res.

-spec render(doc()) -> string().
render(D) ->
    prettypr:format(D, 200).


-spec with_parens(boolean(), doc()) -> doc().
with_parens(false, D) -> D;
with_parens(true, D) -> parens(D).

-spec render_list(fun((T) -> doc()), list(T)) -> string().
render_list(Fun, L) ->
    render(comma_sep(lists:map(Fun, L))).

-spec render_list(string(), [T], fun((T) -> doc())) -> string().
render_list(Sep, L, F) ->
    render(sep_by(text(Sep), lists:map(F, L))).