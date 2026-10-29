import fundamental_group_free_group_covers as fc


def test_reduce_word():
    assert fc.reduce_word("") == ""
    assert fc.reduce_word("aA") == ""
    assert fc.reduce_word("abBA") == ""
    assert fc.reduce_word("aAbaB") == "baB"
    assert fc.reduce_word("abAB") == "abAB"
    # reduction is idempotent
    for w in ("aabBAb", "BBbbaA", "abABba"):
        assert fc.reduce_word(fc.reduce_word(w)) == fc.reduce_word(w)


def test_inverse_word():
    for w in ("ab", "abAB", "aaBBa"):
        assert fc.reduce_word(w + fc.inverse_word(w)) == ""
        assert fc.reduce_word(fc.inverse_word(w) + w) == ""


def test_reduced_word_counts():
    for k in range(1, 6):
        assert len(fc.reduced_words(k)) == 4 * 3 ** (k - 1)


def test_action_is_a_homomorphism():
    sigma, tau = (1, 0, 2), (0, 2, 1)
    words = ["a", "b", "ab", "ba", "abAB", "aB"]
    for u in words:
        for v in words:
            assert fc.act(u + v, sigma, tau) == fc.compose(fc.act(u, sigma, tau),
                                                           fc.act(v, sigma, tau))
    assert fc.act("aA", sigma, tau) == (0, 1, 2)
    assert fc.act("ab", sigma, tau) != fc.act("ba", sigma, tau)


def test_transitivity():
    assert fc.is_transitive((1, 0, 2), (0, 2, 1))
    assert not fc.is_transitive((1, 0, 2), (1, 0, 2))
    assert fc.is_transitive((0,), (0,))


def test_subgroup_and_cover_counts():
    assert [fc.subgroups_of_index(n) for n in range(1, 6)] == [1, 3, 13, 71, 461]
    assert [fc.connected_covers(n) for n in range(1, 5)] == [1, 3, 7, 26]
    assert [len(fc.transitive_pairs(n)) for n in range(1, 5)] == [1, 3, 26, 426]
