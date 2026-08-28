import Lake
open Lake DSL

package «nabla_proof» where
  -- 設定編譯選項，關閉自動隱式變數以確保語法嚴謹
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- 引入 Palomar 自動化建置所需的 Mathlib 依賴庫
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- 宣告 Challenge 模組目標（對應 Challenge.lean）
lean_lib «Challenge» where

-- 宣告 Solution 模組目標（對應 Solution.lean，設為預設建置目標）
@[default_target]
lean_lib «Solution» where