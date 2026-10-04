"""Compare a short direct simultaneous-play prefix with event jumps."""

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "computations"))
import exact_events

_, scale, matrix = exact_events.load(2)
initial = [row[0] for row in matrix]
direct = exact_events.stepwise(initial, matrix, 1000)
jumped = exact_events.jump_to(initial, matrix, 1000)
assert direct == jumped
print("1000 post-setup rounds agree exactly; score scale:", scale)
print("Counts after those rounds:", direct[1])
