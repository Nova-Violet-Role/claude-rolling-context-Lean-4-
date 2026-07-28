/-
Copyright (c) 2026 Saimono. All rights reserved.
SPDX-FileCopyrightText: 2026 Saimono / Nova-Violet Role
SPDX-License-Identifier: AGPL-3.0-or-later OR EUPL-1.2
See NOTICE.md at the repository root for the full licence map.
Authors: Saimono
-/
import Mathlib

/-! # `decide` vs `norm_num` on `Nat.Prime` -/

theorem p17_decide : Nat.Prime 17 := by decide

theorem p17_normnum : Nat.Prime 17 := by norm_num

theorem p17_term : Nat.Prime 17 := by exact Nat.prime_iff.mpr (by decide)

-- scaling probe
theorem p104729_normnum : Nat.Prime 104729 := by norm_num

#print axioms p17_decide
#print axioms p17_normnum
