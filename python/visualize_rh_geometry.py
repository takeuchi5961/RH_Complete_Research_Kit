import numpy as np
import matplotlib.pyplot as plt

def complex_D_model(R, theta):
    # f(R, theta) = R + (1 - R) * exp(-i * theta)
    return R + (1 - R) * (np.cos(-theta) + 1j * np.sin(-theta))

thetas = np.linspace(0, 2*np.pi, 500)
R_values = [0.3, 0.5, 0.7]
colors = ['blue', 'red', 'green']

plt.figure(figsize=(8, 8))
plt.axhline(0, color='black', linewidth=1)
plt.axvline(0, color='black', linewidth=1)

for R, color in zip(R_values, colors):
    path = complex_D_model(R, thetas)
    label = f'R = {R}' + (' (Critical Line)' if R == 0.5 else '')
    plt.plot(path.real, path.imag, label=label, color=color, linewidth=2 if R==0.5 else 1)
    
    # theta = pi の地点をプロット
    point_pi = complex_D_model(R, np.pi)
    plt.scatter(point_pi.real, point_pi.imag, color=color)
    plt.text(point_pi.real, point_pi.imag + 0.05, f'θ=π (R={R})', ha='center')

plt.title("Locus of Point D in Complex Plane\n$f(R, θ) = R + (1-R)e^{-iθ}$")
plt.xlabel("Real Part")
plt.ylabel("Imaginary Part")
plt.legend()
plt.grid(True, linestyle='--', alpha=0.7)
plt.axis('equal')
plt.show()