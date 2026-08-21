import numpy as np

A = np.array([
    [0, 0, 1],
    [-1, 0, -3],
    [0, -1, 0]
], dtype=object)

B = np.array([
    [-1, 0, -1],
    [1, -1, 3],
    [0, 1, -1]
], dtype=object)

C = np.array([
    [4, -3, -10],
    [-1, 1, 3],
    [-1, 1, 4]
], dtype=object)

# Check if A and B commute
AB = np.dot(A, B)
BA = np.dot(B, A)
print("AB == BA:", np.array_equal(AB, BA))
