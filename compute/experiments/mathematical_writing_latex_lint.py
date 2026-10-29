r"""A small LaTeX linter: the mechanical part of careful writing.

Some writing faults are mechanical enough for a program to find. This linter
reads a LaTeX fragment and reports:

* environments that are opened and never closed (or closed out of order);
* \ref and \eqref to labels that do not exist;
* macros that are used but neither standard nor defined by \newcommand;
* sentences that begin with a formula (hard to read: "$n$ is prime" after
  a full stop looks like a continuation);
* words that assert ease instead of giving a reason ("clearly", "obviously").

We lint a draft paragraph and its revision. The checks are exact for the text
given, but they are heuristics about style: they find no mathematical errors,
and a clean report does not mean the writing is good.
"""

import re

EXPERIMENT = {
    "id": "mathematical_writing_latex_lint",
    "title": "Linting LaTeX: environments, references, macros and style flags",
    "evidence": ["exact"],
    "lessons": ["mathematical-writing"],
    "summary": (
        "Checks a draft and a revised LaTeX fragment for unbalanced environments, "
        "references to missing labels, undefined macros, sentences that start with "
        "a formula and words like 'clearly'. The analysis of the given text is exact, "
        "but these are mechanical style checks: they cannot detect mathematical "
        "errors."
    ),
    "packages": [],
}

#: Commands a document with amsmath and amsthm may use without defining them.
STANDARD = {
    "begin", "end", "label", "ref", "eqref", "cite", "emph", "textbf", "frac",
    "mathbb", "mathrm", "sum", "prod", "le", "ge", "ne", "in", "cdot", "dots",
    "ldots", "mid", "nmid", "equiv", "pmod", "bmod", "to", "mapsto", "infty",
    "alpha", "beta", "gamma", "delta", "varepsilon", "lambda", "pi", "sqrt",
    "left", "right", "quad", "qquad", "text", "newcommand", "section",
    "subsection", "item", "forall", "exists", "neg", "wedge", "vee", "sim",
    "binom", "lfloor", "rfloor", "colon", "subseteq", "cup", "cap", "setminus",
    "gcd",
}
STYLE_WORDS = ("clearly", "obviously", "trivially", "it is easy to see")

DRAFT = r"""
\begin{theorem}\label{thm:main}
$n^2-1$ is divisible by $24$ for $p>3$ prime.
\end{theorem}
\begin{proof}
Clearly $p^2 - 1 = (p-1)(p+1)$. $p$ is odd so both factors are even, and
one is divisible by $4$. One of $p-1,p,p+1$ is a multiple of $3$, so we are
done by Lemma~\ref{lem:three} and \Ztwo-arguments.
\end{theorem}
"""

REVISION = r"""
\newcommand{\Z}{\mathbb{Z}}
\begin{lemma}\label{lem:three}
Among any three consecutive integers, exactly one is divisible by $3$.
\end{lemma}
\begin{theorem}\label{thm:main}
If $p > 3$ is prime, then $24 \mid p^2 - 1$.
\end{theorem}
\begin{proof}
Write $p^2 - 1 = (p - 1)(p + 1)$. Since $p$ is odd, $p - 1$ and $p + 1$
are consecutive even numbers, so one of them is divisible by $4$ and
$8 \mid p^2 - 1$. By Lemma~\ref{lem:three}, one of $p - 1, p, p + 1$ is
divisible by $3$; it is not $p$, since $p > 3$ is prime. Hence
$3 \mid p^2 - 1$, and as $\gcd(3, 8) = 1$, we get $24 \mid p^2 - 1$
in $\Z$.
\end{proof}
"""


def environment_problems(text):
    """Unclosed or mismatched \\begin/\\end pairs."""
    stack, problems = [], []
    for kind, name in re.findall(r"\\(begin|end)\{(\w+)\}", text):
        if kind == "begin":
            stack.append(name)
        elif not stack or stack[-1] != name:
            opened = stack[-1] if stack else "nothing"
            problems.append(f"\\end{{{name}}} closes {opened}")
            if stack:
                stack.pop()
        else:
            stack.pop()
    problems += [f"\\begin{{{name}}} never closed" for name in stack]
    return problems


def missing_labels(text):
    """References whose label is not defined in the text."""
    labels = set(re.findall(r"\\label\{([^}]*)\}", text))
    refs = re.findall(r"\\(?:eq)?ref\{([^}]*)\}", text)
    return sorted({r for r in refs if r not in labels})


def undefined_macros(text):
    """Macros used but neither standard nor defined with \\newcommand."""
    defined = set(re.findall(r"\\newcommand\{\\(\w+)\}", text))
    used = set(re.findall(r"\\([A-Za-z]+)", text))
    return sorted(used - STANDARD - defined)


def sentences_starting_with_math(text):
    """Sentences beginning with $ (after . ! ? or at the start of an
    environment); line breaks inside a paragraph are ignored."""
    body = re.sub(r"\\(begin|end)\{\w+\}(\\label\{[^}]*\})?", ". ", text)
    body = " ".join(body.split())
    return len(re.findall(r"[.!?]\s+\$", body))


def style_flags(text):
    lower = text.lower()
    return [w for w in STYLE_WORDS if w in lower]


def report(name, text):
    lines = [f"{name}:"]
    checks = [
        ("environments", environment_problems(text)),
        ("missing labels", missing_labels(text)),
        ("undefined macros", ["\\" + m for m in undefined_macros(text)]),
        ("style words", style_flags(text)),
    ]
    for title, found in checks:
        lines.append(f"  {title:<17} {', '.join(found) if found else 'none'}")
    lines.append(f"  {'formula-initial':<17} {sentences_starting_with_math(text)}"
                 " sentence(s)")
    return lines


def main():
    for line in report("Draft", DRAFT) + [""] + report("Revision", REVISION):
        print(line)
    print()
    print("Not detected by any linter: the draft's theorem says n where it")
    print("means p, and its proof never explains why the multiple of 3 is not")
    print("p itself. Only a careful reader (or a proof assistant) catches that.")
    print()
    print("Epistemic status: exact pattern matching on the two fragments shown.")
    print("The checks are heuristics about mechanics and style; a clean report")
    print("says nothing about whether the mathematics is correct or clear.")


if __name__ == "__main__":
    main()
