"""Shared pytest configuration for the Lumenary compute experiments.

Puts ``compute/experiments`` (and ``compute`` itself, for ``verify.py``) on
``sys.path`` so tests can ``import set_identities`` etc. exactly as the
browser does: each experiment is a single, self-contained module.
"""

import importlib
import pathlib
import sys

import pytest

# Do not litter compute/ with __pycache__ when experiments are imported.
sys.dont_write_bytecode = True

COMPUTE_DIR = pathlib.Path(__file__).resolve().parent.parent
EXPERIMENTS_DIR = COMPUTE_DIR / "experiments"
REPO_ROOT = COMPUTE_DIR.parent

for path in (EXPERIMENTS_DIR, COMPUTE_DIR):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

#: The experiment ids the website references. Keep in sync with docs/compute.md.
EXPECTED_IDS = [
    "collections_sorting",
    "set_identities",
    "integer_inverses",
    "sign_rules",
    "counting_functions",
    "composition_check",
    "clock_arithmetic",
    "remainder_families",
    "euler_polynomial",
    "exact_vs_numerical",
    "cantor_diagonal",
    "random_walk_statistics",
]


def experiment_ids():
    """Ids of every experiment file present on disk, sorted."""
    return sorted(p.stem for p in EXPERIMENTS_DIR.glob("*.py") if not p.name.startswith("_"))


def load_experiment(experiment_id):
    """Import (or re-use) the experiment module with the given id."""
    return importlib.import_module(experiment_id)


@pytest.fixture(scope="session")
def repo_root():
    return REPO_ROOT
