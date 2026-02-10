$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $PSScriptRoot
Set-Location $root

$outDir = Join-Path $root "data"
if (-not (Test-Path $outDir)) {
  New-Item -Path $outDir -ItemType Directory -Force | Out-Null
}
$outCsv = Join-Path $outDir "abcd_overlap_0p1_to_0p9_step0p01.csv"

# 視覚的に重なって見える閾値（表示スケール依存）
$visualEps = 0.02
$zero = [decimal]0

$rows = New-Object System.Collections.Generic.List[object]
for ($i = 10; $i -le 90; $i++) {
  [decimal]$R  = [decimal]$i / [decimal]100

  # 幾何定義
  [decimal]$A_x = -$R
  [decimal]$B_x =  $R
  [decimal]$Dx = [decimal]2 * $R - [decimal]1   # θ=π のとき
  [decimal]$Dy = [decimal]0

  $absDx = [math]::Abs([double]$Dx)
  $absDy = [math]::Abs([double]$Dy)
  $dist0 = [math]::Sqrt($absDx * $absDx + $absDy * $absDy)

  $exactOverlap = (($Dx -eq $zero) -and ($Dy -eq $zero))
  $visualOverlap = ($dist0 -le $visualEps)

  $rows.Add([pscustomobject]@{
    R = "{0:N2}" -f [double]$R
    A_x = "{0:N2}" -f [double]$A_x
    B_x = "{0:N2}" -f [double]$B_x
    Dx_at_pi = "{0:N8}" -f [double]$Dx
    Dy_at_pi = "{0:N8}" -f [double]$Dy
    Dist_to_Origin = "{0:N8}" -f $dist0
    Delta_R_from_0p5 = "{0:N2}" -f ([double]$R - 0.5)
    Exact_Overlap_At_Origin = $exactOverlap
    Visual_Overlap_Eps_0p02 = $visualOverlap
  }) | Out-Null
}

$rows | Export-Csv -Path $outCsv -NoTypeInformation -Encoding UTF8

Write-Host "[OK] CSV出力: $outCsv" -ForegroundColor Green
Write-Host ""
Write-Host "[Key rows: R=0.49, 0.50, 0.51]" -ForegroundColor Cyan
$rows | Where-Object { $_.R -in @("0.49","0.50","0.51") } | Format-Table -AutoSize
