import numpy as np
import matplotlib.pyplot as plt

# 最初の零点付近
t = 14.134725141  # 最初の零点
N = 100  # 表示する項数

x, y = [0], [0]  # 原点スタート
for n in range(1, N+1):
    dx = (-1)**(n-1) / np.sqrt(n) * np.cos(t * np.log(n))
    dy = (-1)**(n-1) / np.sqrt(n) * np.sin(t * np.log(n))
    x.append(x[-1]+dx)
    y.append(y[-1]+dy)

plt.figure(figsize=(6,6))
plt.plot(x, y, marker='o', markersize=3, linestyle='-')
plt.plot(0, 0, 'r*', markersize=12)  # 原点
plt.title("幾何学的ゼータベクトル螺旋 (σ=1/2, t=t₁)")
plt.axis('equal')
plt.show()
