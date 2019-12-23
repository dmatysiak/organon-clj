# organon

## Grammar

    <PROPOSITION> ::=
        <QN><TERM><COPULA><TERM>
        <QN><TERM><COPULA><QL><TERM>
        <SIGN><QN><TERM><COPULA><TERM>
        <SIGN><QN><TERM><COPULA><QL><TERM>
        <SIGNQN><TERM><COPULA><TERM>
        <SIGNQN><TERM><COPULA><QL><TERM>

    <SIGN>   ::= not
    <QN>     ::= every | some
    <TERM>   ::= <VAR> | <CONST> | <CONJ>
    <COPULA> ::= is | is not | is a | is not a
    <QL>     ::= un | non
    <CONJ>   ::= both <TERM> and <TERM> (and <TERM>)*

`<TERM>` must also allow for expressing relations, e.g.:

    <QN><TERM><COPULA><TERM><PREPOSITION><QN><TERM>

where `<PREPOSITION>` is something like "of", "to", "from".
