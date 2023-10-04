predicate {:opaque} secretPredicate(q: int)
{
    q > 1234
}

function magicNum(): int
{
    reveal_secretPredicate();
    assert secretPredicate(31984823);
    15213
}

lemma fooLemma(q: int)
    requires secretPredicate(q)

lemma barLemma(q: int)
    requires secretPredicate(q)
{
    if q > 6789 {
        fooLemma(q - 1);
    }
}
