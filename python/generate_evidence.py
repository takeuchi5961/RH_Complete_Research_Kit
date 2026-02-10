import numpy as np
from scipy.special import zeta
import pandas as pd
import os

# 保存先のパスを設定（reproducibilityフォルダへ）
save_dir = r"C:\Users\banbo\Desktop\RH_Complete_Research_Kit_v6_ALL_FIXED\reproducibility"
if not os.path.exists(save_dir):
    os.makedirs(save_dir)

save_path = os.path.join(save_dir, "Zeta_Numerical_Evidence.csv")

# 最初の10個の零点の虚部(t)
zeros_t = [14.1347, 21.0220, 25.0109, 30.4249, 32.9351, 37.5862, 40.9187, 43.3271, 48.0052, 49.7738]
epsilon = 0.01  # 偏差

data = []
for t in zeros_t:
    abs_val_crit = np.abs(zeta(0.5 + 1j*t))
    abs_val_dev = np.abs(zeta(0.5 + epsilon + 1j*t))
    data.append({
        "t_value": t,
        "sigma_critical": 0.5,
        "abs_zeta_at_0.5": abs_val_crit,
        "sigma_deviated": 0.51,
        "abs_zeta_at_0.51": abs_val_dev,
        "gap_observed": abs_val_dev - abs_val_crit
    })

df = pd.DataFrame(data)
df.to_csv(save_path, index=False)
print(f"✅ 数値エビデンスを保存しました: {save_path}")