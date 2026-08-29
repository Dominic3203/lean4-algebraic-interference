import Lake
open Lake DSL

package «nabla_field_annihilation» where
  -- Project Metadata
  keywords := #["math.CO", "combinatorics", "boolean-hypercube", "nabla-field"]
  
  -- Lake Configuration
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints 'λ' as 'λ'
    ⟨`autoImplicit, false⟩  -- forces explicit variable declarations for proof safety
  ]

-- 引入 Palomar 自動化建置所需的 Mathlib 依賴庫
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- 宣告 Challenge 模組目標（對應 Challenge.lean）
lean_lib «Challenge» where

-- 宣告 Solution 模組目標（對應 Solution.lean，設為預設建置目標）
@[default_target]
lean_lib «Solution» where