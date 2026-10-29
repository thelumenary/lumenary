import math

import loops_and_conditions_loops as lp


def closes(repeats, angle):
    (x, y), _ = lp.turtle_loop(repeats, angle)
    return math.hypot(x, y) < 1e-9


def test_regular_polygons_close():
    for n in range(3, 13):
        assert closes(n, 360 / n)
    assert closes(5, 144)  # the five-pointed star turns twice round


def test_open_paths():
    assert not closes(3, 60)
    assert not closes(4, 60)
    (x, y), turned = lp.turtle_loop(3, 60)
    assert abs(math.hypot(x, y) - 2) < 1e-9 and turned == 180


def test_square_corners():
    (x, y), turned = lp.turtle_loop(1, 90)
    assert abs(x) < 1e-12 and abs(y - 1) < 1e-12 and turned == 90
    (x, y), _ = lp.turtle_loop(2, 90)
    assert abs(x - 1) < 1e-12 and abs(y - 1) < 1e-12


def test_repeat_until():
    assert lp.repeat_until(0, lambda n: n + 3, lambda n: n > 20) == (21, 7, True)
    assert lp.repeat_until(10, lambda n: n - 2, lambda n: n == 0) == (0, 5, True)
    number, steps, stopped = lp.repeat_until(9, lambda n: n - 2, lambda n: n == 0)
    assert not stopped and steps == 1000 and number == 9 - 2000
    assert lp.repeat_until(5, lambda n: n, lambda n: True) == (5, 0, True)
