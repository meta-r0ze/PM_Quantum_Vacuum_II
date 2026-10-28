"""Floating-point diagnostic, NOT a Lean proof or a physical parameter fit.
Run with Python, NumPy and SciPy. Compares the original and vacuum-preserving orderings.
"""
import numpy as np
from scipy.linalg import expm, eigvals

beta = np.block([[np.zeros((2, 2)), np.eye(2)], [np.eye(2), np.zeros((2, 2))]])
gamma = np.diag([1, 1, -1, -1])
plus, minus = (np.eye(4) + gamma) / 2, (np.eye(4) - gamma) / 2
beta8 = np.block([[beta, np.zeros((4, 4))], [np.zeros((4, 4)), beta]])
hop = np.block([[np.zeros((4, 4)), -beta @ plus], [-beta @ minus, np.zeros((4, 4))]])
zero_basis = np.eye(8)[:, [0, 1, 6, 7]]
for tau in (0.1, 0.25, 0.5):
    r = np.cos(tau) * np.eye(8) + 1j * np.sin(tau) * beta8
    original = expm(-1j * tau * (3 * beta8 + hop)) @ r @ r @ r
    corrected = expm(-1j * tau * hop) @ np.linalg.matrix_power(r.conj().T, 3) @ r @ r @ r
    for name, u in (("original", original), ("vacuum-preserving", corrected)):
        displacement = np.max(np.abs(u @ zero_basis - zero_basis))
        phases = np.sort(np.abs(np.angle(eigvals(u))))
        print(f"{name}, tau={tau}: max zero-basis displacement={displacement:.9g}; "
              f"four nearest eigenphase magnitudes={phases[:4]}")
