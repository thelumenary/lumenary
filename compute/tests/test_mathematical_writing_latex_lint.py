import mathematical_writing_latex_lint as ml


def test_draft_problems_found():
    assert ml.environment_problems(ml.DRAFT) == ["\\end{theorem} closes proof"]
    assert ml.missing_labels(ml.DRAFT) == ["lem:three"]
    assert ml.undefined_macros(ml.DRAFT) == ["Ztwo"]
    assert ml.style_flags(ml.DRAFT) == ["clearly"]
    assert ml.sentences_starting_with_math(ml.DRAFT) == 2


def test_revision_is_clean():
    assert ml.environment_problems(ml.REVISION) == []
    assert ml.missing_labels(ml.REVISION) == []
    assert ml.undefined_macros(ml.REVISION) == []
    assert ml.style_flags(ml.REVISION) == []
    assert ml.sentences_starting_with_math(ml.REVISION) == 0


def test_environment_edge_cases():
    assert ml.environment_problems(r"\begin{proof}") == ["\\begin{proof} never closed"]
    assert ml.environment_problems(r"\end{proof}") == ["\\end{proof} closes nothing"]
    nested = r"\begin{theorem}\begin{equation}x\end{equation}\end{theorem}"
    assert ml.environment_problems(nested) == []


def test_newcommand_and_eqref():
    text = r"\newcommand{\R}{\mathbb{R}} $x \in \R$ by \eqref{eq:1}. \label{eq:1}"
    assert ml.undefined_macros(text) == []
    assert ml.missing_labels(text) == []
    assert ml.missing_labels(r"see \ref{nowhere}") == ["nowhere"]


def test_formula_initial_ignores_line_breaks():
    text = "We have\n$x = 1$ here. $y$ is new."
    assert ml.sentences_starting_with_math(text) == 1
