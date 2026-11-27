/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3Head
public import HlawkaSchatten.BelowExponent.G3HeadData
import all HlawkaSchatten.BelowExponent.G3Head
import all HlawkaSchatten.BelowExponent.G1
import all HlawkaSchatten.BelowExponent.G3
import all HlawkaSchatten.BelowExponent.G3HeadData

/-! Soundness of the exact endpoint certificate and the full G3 head chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set

open private head_q_lo head_q_hi head_q_pos head_center_bounds head_jensen_bound
  head_far_bound head_outside_middle head_gap_div_h head_secant head_middle_interpolate
  from HlawkaSchatten.BelowExponent.G3Head
open private evenGap_nonneg from HlawkaSchatten.BelowExponent.G1
open private g3_k_max from HlawkaSchatten.BelowExponent.G3
open G3HeadData
open private headCornerChecks from HlawkaSchatten.BelowExponent.G3HeadData

private theorem headQL_le : (headQL:ℝ) ≤ criticalQ :=
  (by norm_num [headQL] : (headQL:ℝ)≤1054/665).trans criticalQ_bracket.1.le

private theorem head_power_sound (n : ℕ) (hn : n≤2048) :
    (headLower n : ℝ) ≤ ((n:ℝ)/1024)^criticalQ ∧
      ((n:ℝ)/1024)^criticalQ ≤ (headUpper n : ℝ) := by
  have h := headPowerChecks (⟨n,by omega⟩:Fin 2049)
  have hqLo : (84/53:ℝ) ≤ criticalQ := by simpa [headQL] using headQL_le
  by_cases hn' : n≤1024
  · have hs : (headPower n).1^41*1024^65 ≤ n^65*headScale^41 ∧
        n^84*headScale^53 ≤ (headPower n).2^53*1024^84 := by
      simpa only [headPowerOK,ite_eq_left hn'] using h
    have h₁ := (le_natRat_rpow_iff (a:=n) (m:=65) (n:=41)
      (by decide : 0<(1024:ℕ)) (by decide : 0<headScale) (by decide)).mpr hs.1
    have h₂ := (natRat_rpow_le_iff (a:=n) (m:=84) (n:=53)
      (by decide : 0<(1024:ℕ)) (by decide : 0<headScale) (by decide)).mpr hs.2
    simp only [Nat.cast_ofNat] at h₁ h₂
    have hx : (n:ℝ)/1024≤1 := (div_le_one₀ (by norm_num : (0:ℝ)<1024)).mpr (by exact_mod_cast hn')
    unfold headLower headUpper
    push_cast
    refine ⟨h₁.trans ?_, ?_⟩
    · exact Real.rpow_le_rpow_of_exponent_ge' (by positivity) hx (zero_le_one.trans head_q_pos.le) head_q_hi
    · exact (Real.rpow_le_rpow_of_exponent_ge' (by positivity) hx (by norm_num) hqLo).trans h₂
  · have hs : (headPower n).1^53*1024^84 ≤ n^84*headScale^53 ∧
        n^65*headScale^41 ≤ (headPower n).2^41*1024^65 := by
      simpa only [headPowerOK,ite_eq_right hn'] using h
    have h₁ := (le_natRat_rpow_iff (a:=n) (m:=84) (n:=53)
      (by decide : 0<(1024:ℕ)) (by decide : 0<headScale) (by decide)).mpr hs.1
    have h₂ := (natRat_rpow_le_iff (a:=n) (m:=65) (n:=41)
      (by decide : 0<(1024:ℕ)) (by decide : 0<headScale) (by decide)).mpr hs.2
    simp only [Nat.cast_ofNat] at h₁ h₂
    have hx : 1≤(n:ℝ)/1024 := (le_div_iff₀ (by norm_num : (0:ℝ)<1024)).mpr (by
      rw [one_mul]; exact_mod_cast (le_of_not_ge hn'))
    unfold headLower headUpper
    push_cast
    exact ⟨h₁.trans (Real.rpow_le_rpow_of_exponent_le hx hqLo),
      (Real.rpow_le_rpow_of_exponent_le hx head_q_hi).trans h₂⟩

private theorem head_ratio_bound (σ : ℝ) (hσ : 0<σ) (hσ₁ : σ≤1/5) :
    (1/g3Weight 0 σ-1)*(σ/(2-σ))^(criticalQ-1) ≤ 3/4 := by
  obtain ⟨i, hi₀,hi₁⟩ := exists_adjacent_knots 49 (f:=fun i => (i.val:ℝ)/250)
    (by simpa using hσ.le) (by
      have h : ((Fin.last 50).val:ℝ)/250=(1/5:ℝ) := by norm_num [Fin.last]
      rw [h]; exact hσ₁)
  have hi₁' : σ≤((i.val+1:ℕ):ℝ)/250 := hi₁
  simp only [Nat.cast_add, Nat.cast_one] at hi₁'
  let j := (i.val:ℝ)
  have hj : j≤49 := by dsimp [j]; exact_mod_cast (show i.val≤49 by omega)
  have hDen : 0<499-i.val := by omega
  have hDenR : (0:ℝ)<499-j := by
    dsimp [j]; linarith
  let x := σ^(12/25:ℝ)
  let y := σ^(criticalQ-1-12/25)
  let z := (1/(2-σ))^(criticalQ-1)
  have hx : 0<x := Real.rpow_pos_of_pos hσ _
  have hxp : x≤1 := Real.rpow_le_one (by linarith : 0≤σ) (by linarith : σ≤1) (by norm_num)
  have hy : 0≤y := Real.rpow_nonneg hσ.le _
  have hσden : 0<2-σ := by linarith
  have hz : 0≤z := Real.rpow_nonneg (by positivity) _
  obtain ⟨hl,hr,hinv,hc⟩ := headRatioChecks i
  have hxL : (headRatioLeft i:ℝ)≤x := by
    have h := (le_natRat_rpow_iff (a:=i.val) (m:=12) (n:=25)
      (by decide : 0<(250:ℕ)) (by decide : 0<headScale) (by decide)).mpr hl
    unfold headRatioLeft
    push_cast
    exact h.trans (Real.rpow_le_rpow (by positivity) hi₀ (by norm_num))
  have hyU : y≤(headRatioRise i:ℝ) := by
    have h := (natRat_rpow_le_iff (a:=i.val+1) (m:=139) (n:=1325)
      (by decide : 0<(250:ℕ)) (by decide : 0<headScale) (by decide)).mpr hr
    have hExp' : (139/1325:ℝ)≤criticalQ-1-12/25 := by
      have hq : (84/53:ℝ)≤criticalQ := by simpa [headQL] using headQL_le
      linarith only [hq]
    unfold headRatioRise
    push_cast
    exact (Real.rpow_le_rpow_of_exponent_ge hσ (by linarith) hExp').trans
      ((Real.rpow_le_rpow hσ.le hi₁ (by norm_num)).trans h)
  have hzU : z≤(headRatioInv i:ℝ) := by
    have h := (natRat_rpow_le_iff (a:=250) (m:=31) (n:=53)
      hDen (by decide : 0<headScale) (by decide)).mpr hinv
    simp only [Nat.cast_ofNat, Nat.cast_sub (show i.val≤499 by omega)] at h
    have hRatio : 1/(2-σ)≤250/(499-j) := by
      apply (div_le_div_iff₀ hσden hDenR).2
      dsimp [j]
      linarith only [hi₁']
    have hExp : (31/53:ℝ)≤criticalQ-1 := by
      have hq : (84/53:ℝ)≤criticalQ := by simpa [headQL] using headQL_le
      linarith only [hq]
    have hBase : 1/(2-σ)≤1 := (div_le_one₀ hσden).mpr (by linarith)
    unfold headRatioInv
    push_cast
    exact (Real.rpow_le_rpow_of_exponent_ge (by positivity) hBase hExp).trans
      ((Real.rpow_le_rpow (by positivity) hRatio (by norm_num)).trans h)
  have hw₀ : (147/250)*x ≤ g3Weight 0 σ := by
    have h : (49/50:ℝ)≤(if σ<3/20 then (1:ℝ) else 49/50) := by split <;> norm_num
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h (by norm_num : (0:ℝ)≤3/5)) hx.le
    unfold g3Weight
    norm_num [x] at hm ⊢
    exact hm
  have hInv := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1) (by positivity :
    0<(147/250:ℝ)*x) hw₀
  have hkEq : (σ/(2-σ))^(criticalQ-1) = x*y*z := by
    unfold x y z
    rw [← Real.rpow_add hσ, show (12/25:ℝ)+(criticalQ-1-12/25)=criticalQ-1 by ring,
      Real.div_rpow hσ.le hσden.le,one_div,Real.inv_rpow hσden.le,div_eq_mul_inv]
  have hcR := (Rat.cast_le (K:=ℝ)).mpr hc
  change ((250/147-headRatioLeft i)*headRatioRise i*headRatioInv i : ℚ) ≤ _ at hc
  push_cast at hcR
  calc
    _ ≤ (1/((147/250)*x)-1)*((σ/(2-σ))^(criticalQ-1)) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_right hInv _) (Real.rpow_nonneg (by positivity) _)
    _ = (250/147-x)*y*z := by rw [hkEq]; field_simp [hx.ne']
    _ ≤ ((250/147)-(headRatioLeft i:ℝ))*(headRatioRise i:ℝ)*(headRatioInv i:ℝ) := by
      have hh : 0≤(250/147:ℝ)-(headRatioLeft i:ℝ) := by linarith only [hxp,hxL]
      exact mul_le_mul (mul_le_mul (sub_le_sub_left hxL _) hyU hy hh) hzU hz
        (mul_nonneg hh (hy.trans hyU))
    _ ≤ _ := hcR

private theorem head_ratio_at_depth {h h₀ σ U : ℝ}
    (hh₀ : 0≤h₀) (hh : h₀≤h) (hh₁ : h≤1) (hσ : 0<σ) (hσ₁ : σ≤1/5)
    (hU₀ : 0≤U) (hU : U≤(σ/(2-σ))^(criticalQ-1)) :
    (1/g3Weight h σ-1)*(σ/(2-σ))^(criticalQ-1) ≤ (3/4-(h₀/16)*U)/(1+h₀/16) := by
  let u := (σ/(2-σ))^(criticalQ-1)
  let m := g3Weight h σ
  let m₀ := g3Weight 0 σ
  have hp := g3_weight_pos_lt_third (hh₀.trans hh) hh₁ hσ hσ₁
  have hp₀ := (g3_weight_pos_lt_third (h:=0) le_rfl zero_le_one hσ hσ₁).1
  have hm : m=(1+h/16)*m₀ := by dsimp [m,m₀]; unfold g3Weight; ring
  have hr₀ : 0≤(1/m-1)*u := by
    apply mul_nonneg _ (hU₀.trans hU)
    have hk : 1≤1/m := (le_div_iff₀ hp.1).mpr (by linarith only [hp.2])
    linarith only [hk]
  have heq : ((1/m-1)*u)*(1+h/16)=(1/m₀-1)*u-(h/16)*u := by
    have hK : 1+h/16≠0 := by linarith [hh₀.trans hh]
    have hInv : (1/m)*(1+h/16)=1/m₀ := by
      rw [hm,one_div,mul_inv_rev,mul_assoc,inv_mul_cancel₀ hK,mul_one,← one_div]
    calc
      _ = ((1/m)*(1+h/16)-(1+h/16))*u := by ring
      _ = _ := by rw [hInv]; ring
  have hR := head_ratio_bound σ hσ hσ₁
  have hU' := mul_le_mul (show h₀/16≤h/16 by linarith only [hh]) hU hU₀
    (by linarith only [hh₀.trans hh])
  apply (le_div_iff₀ (by linarith : 0<1+h₀/16)).2
  calc
    _ ≤ ((1/m-1)*u)*(1+h/16) := mul_le_mul_of_nonneg_left (by linarith) hr₀
    _ = _ := heq
    _ ≤ _ := by linarith only [hR,hU']

private theorem head_pn_upper : ∀ j : Fin 13, headPN j ≤ 64 := by decide +kernel

private theorem head_w_eq (j : Fin 12) : (headW j:ℝ) = 1-(headP j.castSucc:ℝ) := by
  have h := head_pn_upper j.castSucc
  have hn : 0 ≤ 512-headPN j.castSucc := by omega
  have hc : (((512-headPN j.castSucc).toNat:ℕ):ℝ) =
      (↑(512-headPN j.castSucc):ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
  unfold headW headWNum headP
  push_cast
  rw [hc]
  push_cast
  ring

private theorem head_abs_le {p : ℝ} (j : Fin 12)
    (h₀ : (headP j.castSucc:ℝ)≤p) (h₁ : p≤(headP j.succ:ℝ)) :
    (headPAbs j:ℝ) ≤ |p| := by
  have h : 0≤max (0:ℤ) (max (headPN j.castSucc) (-headPN j.succ)) := le_max_left _ _
  unfold headPAbs headPAbsNum
  push_cast
  have he : (((max (0:ℤ) (max (headPN j.castSucc) (-headPN j.succ))).toNat : ℕ):ℝ) =
      ((max (0:ℤ) (max (headPN j.castSucc) (-headPN j.succ)) : ℤ):ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg h
  rw [he,Int.cast_max,Int.cast_max,Int.cast_zero,Int.cast_neg]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<512)).2
  apply max_le (by positivity)
  apply max_le
  · have hh : ((headPN j.castSucc:ℤ):ℝ)/512≤p := by
      simpa [headP, Rat.cast_div] using h₀
    exact (div_le_iff₀ (by norm_num : (0:ℝ)<512)).mp (hh.trans (le_abs_self p))
  · have hh : p≤((headPN j.succ:ℤ):ℝ)/512 := by
      simpa [headP, Rat.cast_div] using h₁
    have hm := (le_div_iff₀ (by norm_num : (0:ℝ)<512)).mp hh
    linarith only [hm,neg_le_abs p]

private theorem head_D_sound (n : ℕ) (y : ℤ)
    (hPlusIdx : (16*(n:ℤ)+y).natAbs≤2048) (hMinusIdx : (16*(n:ℤ)-y).natAbs≤2048) :
    let P := (n:ℝ)/64
    let a := (y:ℝ)/1024
    let D := (|P+a|^criticalQ+|P-a|^criticalQ)/2
    (headDLower n y:ℝ) ≤ D ∧ D ≤ (headDUpper n y:ℝ) := by
  have hs (z : ℤ) (hz : z.natAbs≤2048) :
      (headLower z.natAbs:ℝ)≤|(z:ℝ)/1024|^criticalQ ∧
        |(z:ℝ)/1024|^criticalQ≤(headUpper z.natAbs:ℝ) := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ)≤1024),← Int.cast_abs, ← Nat.cast_natAbs]
    exact head_power_sound _ hz
  have hPlus := hs _ hPlusIdx
  have hMinus := hs _ hMinusIdx
  have hx : ((↑(16*(n:ℤ)+y) : ℝ)/1024)=((n:ℝ)/64)+(y:ℝ)/1024 := by push_cast; ring
  have hy : ((↑(16*(n:ℤ)-y) : ℝ)/1024)=((n:ℝ)/64)-(y:ℝ)/1024 := by push_cast; ring
  rw [hx] at hPlus
  rw [hy] at hMinus
  dsimp [headDLower,headDUpper]
  push_cast
  exact ⟨by linarith only [hPlus.1,hMinus.1],by linarith only [hPlus.2,hMinus.2]⟩

private theorem head_endpoint_sound (i : Fin 4) (upper : Bool) (j : Fin 12) (a : Fin 49) :
    let P := (headCenter upper j:ℝ)
    let H := (headDepth i.succ:ℝ)
    let R := (headR i upper j:ℝ)
    let T := (headT upper j:ℝ)
    let s := (headAngular a:ℝ)
    R*max 0 ((balancedEvenGap criticalQ P ((1-H)*s+H)-balancedEvenGap criticalQ P s)/H)
      +T*s^2+R/(729*H) ≤ (headJLow i upper j:ℝ) := by
  let P := (headCenter upper j:ℝ)
  let H := (headDepth i.succ:ℝ)
  let R := (headR i upper j:ℝ)
  let T := (headT upper j:ℝ)
  let s := (headAngular a:ℝ)
  let n := headCenterNum upper j
  have hPeq : P=(n:ℝ)/64 := by dsimp [P,headCenter,n]; push_cast; rfl
  obtain ⟨hH,hR,_,_,_,_,hc⟩ := headCornerChecks i upper j
  obtain ⟨hA,hB,hC,hD,hE⟩ := hc a
  have h₀ : (headDLower n (32*headAngularNum a):ℝ) ≤
      (|P+s|^criticalQ+|P-s|^criticalQ)/2 := by
    have h := (head_D_sound n (32*headAngularNum a) hA hB).1
    have he : ((↑(32*headAngularNum a):ℝ)/1024)=s := by
      dsimp [s,headAngular]
      push_cast
      ring
    rw [he,←hPeq] at h
    exact h
  have h₁ : (|P+((1-H)*s+H)|^criticalQ+|P-((1-H)*s+H)|^criticalQ)/2 ≤
      (headDUpper n (headYN i a):ℝ) := by
    have h := (head_D_sound n (headYN i a) hC hD).2
    have he : ((headYN i a:ℝ)/1024) = (1-H)*s+H := by
      dsimp [headYN,H,headDepth,s,headAngular]
      push_cast
      ring
    rw [he,←hPeq] at h
    exact h
  change R*max 0 ((balancedEvenGap criticalQ P ((1-H)*s+H)-balancedEvenGap criticalQ P s)/H)
    +T*s^2+R/(729*H)≤_
  have hreal : 0<H := by dsimp [H]; exact_mod_cast hH
  have hnonneg : 0≤R := by dsimp [R]; exact_mod_cast hR
  have hq : (balancedEvenGap criticalQ P ((1-H)*s+H)-balancedEvenGap criticalQ P s)/H ≤
    ((headDUpper n (headYN i a):ℝ)-(headDLower n (32*headAngularNum a):ℝ))/H := by
    apply div_le_div_of_nonneg_right _ hreal.le
    unfold balancedEvenGap
    linarith only [h₀,h₁]
  have hh := mul_le_mul_of_nonneg_left (max_le_max (show (0:ℝ)≤0 from le_rfl) hq) hnonneg
  have he := (Rat.cast_le (K:=ℝ)).mpr hE
  push_cast at he
  refine le_trans ?_ he
  gcongr

private theorem head_middle_cost (i : Fin 4) (upper : Bool) (j : Fin 12)
    {a : ℝ} (ha : -(1/2:ℝ)≤a) (ha' : a≤1) :
    let P := (headCenter upper j:ℝ)
    let H := (headDepth i.succ:ℝ)
    let R := (headR i upper j:ℝ)
    let T := (headT upper j:ℝ)
    R*max 0 ((balancedEvenGap criticalQ P ((1-H)*a+H)-balancedEvenGap criticalQ P a)/H)
      +T*a^2 ≤ (headJLow i upper j:ℝ) := by
  have hL : (headAngular 0:ℝ)≤a := by
    rw [show (headAngular 0:ℝ)=-(1/2:ℝ) by norm_num [headAngular,headAngularNum]]
    exact ha
  have hU : a≤(headAngular (Fin.last 48):ℝ) := by simpa [headAngular,headAngularNum,Fin.last] using ha'
  obtain ⟨d,hd₀,hd₁⟩ := exists_adjacent_knots 47 (f:=fun j => (headAngular j:ℝ)) hL hU
  have hWidth : (headAngular d.succ:ℝ)-(headAngular d.castSucc:ℝ)≤1/32 := by
    unfold headAngular headAngularNum
    push_cast [Fin.val_succ,Fin.val_castSucc]
    linarith
  obtain ⟨hH,hR,hT,_,_,_,_⟩ := headCornerChecks i upper j
  exact head_middle_interpolate (by exact_mod_cast hH) (by exact_mod_cast hR)
    (by exact_mod_cast hT) hd₀ hd₁ hWidth (head_endpoint_sound i upper j d.castSucc)
      (head_endpoint_sound i upper j d.succ)

private theorem head_sigma_bounds {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1/5) :
    ∃ upper : Bool, σ/(2-σ)≤(headKHi upper:ℝ) ∧
      0≤(headKPowerLo upper:ℝ) ∧ (headKPowerLo upper:ℝ)≤(σ/(2-σ))^(criticalQ-1) := by
  by_cases hu : σ<3/20
  · refine ⟨false, ?_, ?_,?_⟩
    · have h : σ/(2-σ)≤3/37 := (div_le_iff₀ (by linarith : 0<2-σ)).2 (by linarith only [hu])
      simpa [headKHi] using h
    · norm_num [headKPowerLo]
    · simpa [headKPowerLo] using Real.rpow_nonneg (div_nonneg hσ.le (by linarith)) (criticalQ-1)
  · refine ⟨true, ?_, ?_,?_⟩
    · simpa [headKHi] using g3_k_max hσ₁
    · norm_num [headKPowerLo]
    · have hk : (3/37:ℝ)≤σ/(2-σ) :=
        (le_div_iff₀ (by linarith : 0<2-σ)).2 (by linarith only [le_of_not_gt hu])
      have hc : (2/9:ℝ)≤(3/37:ℝ)^(24/41:ℝ) := by
        simpa only [Nat.cast_ofNat] using
          (le_natRat_rpow_iff (a:=3) (c:=2) (m:=24) (n:=41)
            (by decide : 0<(37:ℕ)) (by decide : 0<(9:ℕ)) (by decide)).mpr (by decide)
      have hr : (3/37:ℝ)^(24/41:ℝ)≤(3/37:ℝ)^(criticalQ-1) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith only [head_q_hi])
      have h := hc.trans (hr.trans (Real.rpow_le_rpow (by norm_num) hk (sub_nonneg.mpr head_q_pos.le)))
      simpa [headKPowerLo] using h

private theorem head_middle_gap {h σ p s : ℝ} (hh : 0<h) (hσ : 0<σ) (hσ₁ : σ≤1/5)
    (hh₁ : h≤1/(2-σ/(2-σ))) (hp : |p|≤1/8) (hs : |s|≤1/8)
    (hm₀ : -(σ/(2-σ)*(1-p))/2 ≤ s) (hm₁ : s ≤ σ/(2-σ)*(1-p)) :
    0≤g3FacetGap h σ p s 1 := by
  let q := criticalQ
  let k := σ/(2-σ)
  let μ := g3Weight h σ
  let b := 1-μ
  let u := k*(1-p)
  let a := s/u
  let A := balancedEvenGap q p
  let J := balancedJensenGap q (h*k) p 1/(h*k)
  let F := balancedFarIncrement q (1-h) (balancedFarCenter (h*k) (h*k) p 1) s/h
  let ρ := (1/μ-1)*k^(q-1)
  let R₀ := ρ*(1-p)^q
  let T₀ := (9/8)*k*(1-p)^2
  have hhM : h≤17/32 := (g3_h_max hσ₁ hh₁).trans (by norm_num)
  have hhOne : h≤1 := hhM.trans (by norm_num)
  have hk : 0<k := div_pos hσ (by linarith)
  have hw : 0<1-p := by linarith only [(abs_le.mp hp).2]
  have hu : 0<u := mul_pos hk hw
  have hμ := g3_weight_pos_lt_third hh.le hhOne hσ hσ₁
  have hμ₀ : 0<μ := hμ.1
  have hb : 0≤b := by dsimp [b,μ]; linarith only [hμ.2]
  have hρ : 0≤ρ := by
    have ht : 1≤1/μ := (le_div_iff₀ hμ₀).mpr (by dsimp [μ]; linarith only [hμ.2])
    exact mul_nonneg (sub_nonneg.mpr ht) (Real.rpow_nonneg hk.le _)
  have ha₀ : -(1/2:ℝ)≤a := (le_div_iff₀ hu).mpr (by dsimp [u]; linarith only [hm₀])
  have ha₁ : a≤1 := (div_le_one₀ hu).mpr hm₁
  have ht₀ : (headDepth 0:ℝ)≤h := by simpa [headDepth,headDepthNum] using hh.le
  have ht₁ : h≤(headDepth (Fin.last 4):ℝ) := by simpa [headDepth,headDepthNum,Fin.last] using hhM
  obtain ⟨i,hi₀,hi₁⟩ := exists_adjacent_knots 3 (f:=fun j => (headDepth j:ℝ)) ht₀ ht₁
  have hp₀ : (headP 0:ℝ)≤p := by
    rw [show (headP 0:ℝ)=-(1/8:ℝ) by norm_num [headP,headPN]]
    exact (abs_le.mp hp).1
  have hp₁ : p≤(headP (Fin.last 12):ℝ) := by
    rw [show (headP (Fin.last 12):ℝ)=1/8 by norm_num [headP,headPN,Fin.last]]
    exact (abs_le.mp hp).2
  obtain ⟨j,hj₀,hj₁⟩ := exists_adjacent_knots 11 (f:=fun j => (headP j:ℝ)) hp₀ hp₁
  obtain ⟨upper,hkM,hK₀,hK⟩ := head_sigma_bounds hσ hσ₁
  let H := (headDepth i.succ:ℝ)
  let L := (headJLow i upper j:ℝ)
  let R := (headR i upper j:ℝ)
  let T := (headT upper j:ℝ)
  let P := (headCenter upper j:ℝ)
  let W := (headW j:ℝ)
  obtain ⟨hH,hR,hT,hC,hPNum,hWNum,_⟩ := headCornerChecks i upper j
  have hW : 1-p≤W := by dsimp [W]; rw [head_w_eq]; linarith only [hj₀]
  have hP₀ : 0≤P := by
    unfold P headCenter
    push_cast
    positivity
  have hP : P≤|p|/u := by
    apply (le_div_iff₀ hu).2
    have h1 : u≤(headKHi upper:ℝ)*W :=
      mul_le_mul hkM hW hw.le (hk.le.trans hkM)
    have h2 : P*(headKHi upper:ℝ)*W≤(headPAbs j:ℝ) := by
      have h := (Rat.cast_le (K:=ℝ)).mpr hC
      push_cast at h
      exact h
    calc
      _ ≤ P*((headKHi upper:ℝ)*W) := mul_le_mul_of_nonneg_left h1 hP₀
      _ = P*(headKHi upper:ℝ)*W := by ring
      _ ≤ _ := h2.trans (head_abs_le j hj₀ hj₁)
  have hr : R₀≤R := by
    have hDepth₀ : 0≤(headDepth i.castSucc:ℝ) := by unfold headDepth; push_cast; positivity
    have hρU := head_ratio_at_depth hDepth₀ hi₀ hhOne hσ hσ₁ hK₀ hK
    have hPow := (head_power_sound (2*headWNum j) hWNum).2
    push_cast at hPow
    have heq : (2:ℝ)*(headWNum j:ℝ)/1024 = W := by dsimp [W,headW]; push_cast; ring
    rw [heq] at hPow
    have hWpow := (Real.rpow_le_rpow hw.le hW (zero_le_one.trans head_q_pos.le)).trans hPow
    have hR' : R=((3/4-(headDepth i.castSucc:ℝ)/16*(headKPowerLo upper:ℝ))/
        (1+(headDepth i.castSucc:ℝ)/16))*(headUpper (2*headWNum j):ℝ) := by
      dsimp [R,headR]
      push_cast
      rfl
    rw [hR']
    exact mul_le_mul hρU hWpow (Real.rpow_nonneg hw.le _) (hρ.trans hρU)
  have ht : T₀≤T := by
    have ht' : T=(9/8)*(headKHi upper:ℝ)*W^2 := by dsimp [T,headT,W]; push_cast; rfl
    rw [ht']
    have hm := mul_le_mul hkM (pow_le_pow_left₀ hw.le hW 2) (sq_nonneg _) (hk.le.trans hkM)
    have h := mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤9/8)
    dsimp [T₀]
    linarith only [h]
  have hj : L≤J := by
    have hLower := (head_power_sound (2*headPAbsNum j) hPNum).1
    push_cast at hLower
    have heq : (2:ℝ)*(headPAbsNum j:ℝ)/1024=(headPAbs j:ℝ) := by
      unfold headPAbs
      push_cast
      ring
    rw [heq] at hLower
    have hp' : 0≤(headPAbs j:ℝ) := by unfold headPAbs; push_cast; positivity
    have hPpow := hLower.trans (Real.rpow_le_rpow hp' (head_abs_le j hj₀ hj₁)
      (zero_le_one.trans head_q_pos.le))
    have hEnd : (headP j.succ:ℝ)≤1/8 := by
      have hV : (headPN j.succ:ℝ)≤64 := by exact_mod_cast head_pn_upper j.succ
      unfold headP
      push_cast
      linarith only [hV]
    have hProd := mul_le_mul headQL_le (show 1-(headP j.succ:ℝ)≤1-p by linarith only [hj₁])
      (by linarith only [hEnd] : 0≤1-(headP j.succ:ℝ)) (zero_le_one.trans head_q_pos.le)
    have hA := head_center_bounds hh hhM hk (g3_k_max hσ₁) hp
    have hJ := head_jensen_bound (mul_pos hh hk) hA.1 hA.2
    have hMul := mul_le_mul (mul_le_mul hi₁ hkM hk.le (hh.le.trans hi₁))
      (pow_le_pow_left₀ hw.le hW 2) (sq_nonneg _) (mul_nonneg (hh.le.trans hi₁) (hk.le.trans hkM))
    dsimp [L,headJLow]
    push_cast
    change _≤balancedJensenGap q (h*k) p 1/(h*k)
    linarith only [hPpow,hProd,hJ,hMul]
  let Q := max 0 ((balancedEvenGap q P ((1-H)*a+H)-balancedEvenGap q P a)/H)
  have hQ : 0≤Q := le_max_left _ _
  have hSec := head_secant (p:=p) (s:=s) hh hi₁ hu hP₀ hP
  have hFull : R₀*Q+T₀*a^2≤J :=
    (add_le_add (mul_le_mul_of_nonneg_right hr hQ) (mul_le_mul_of_nonneg_right ht (sq_nonneg _))).trans
      ((head_middle_cost i upper j ha₀ ha₁).trans hj)
  have hUeq : b*u^q = μ*k*R₀ := by
    have hK : k^q = k*k^(q-1) := by
      rw [show q=1+(q-1) by ring,Real.rpow_add hk,Real.rpow_one]
      norm_num
    dsimp [u,R₀,ρ,b]
    rw [Real.mul_rpow hk.le hw.le]
    change (1-μ)*(k^q*(1-p)^q) = _
    rw [hK]
    field_simp [hμ₀.ne']
  have hNear := mul_le_mul_of_nonneg_left hSec hb
  change b*((A ((1-h)*s+h*u)-A s)/h)≤b*(u^q*Q) at hNear
  have hNearEq : b*(u^q*Q)=μ*k*R₀*Q := by
    calc
      _ = (b*u^q)*Q := by ring
      _ = _ := by rw [hUeq]
  rw [hNearEq] at hNear
  have hFar := head_far_bound hh hhM (head_center_bounds hh hhM hk (g3_k_max hσ₁) hp).1 hs
  have hFar' : μ*F≤μ*k*(T₀*a^2) := by
    have heq : μ*((9/8)*s^2)=μ*k*(T₀*a^2) := by
      dsimp [T₀,a,u]
      field_simp [hk.ne',hw.ne']
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hFar hμ₀.le
  have hSum := mul_le_mul_of_nonneg_left hFull (mul_nonneg hμ₀.le hk.le)
  have hA := mul_nonneg (mul_nonneg hμ₀.le hk.le) (evenGap_nonneg head_q_pos.le p s)
  suffices H : 0≤g3FacetGap h σ p s 1/h by
    simpa only [zero_mul] using (le_div_iff₀ hh).mp H
  rw [head_gap_div_h hh.ne' hk.ne']
  change 0≤μ*k*(J+A s)+b*((A s-A ((1-h)*s+h*u))/h)-μ*F
  have hCombined : μ*F+b*((A ((1-h)*s+h*u)-A s)/h) ≤ μ*k*J := by
    calc
      _ ≤ μ*k*(T₀*a^2)+μ*k*R₀*Q := add_le_add hFar' hNear
      _ = μ*k*(R₀*Q+T₀*a^2) := by ring
      _ ≤ _ := hSum
  change 0≤μ*k*A s at hA
  calc
    _ ≤ μ*k*J-(μ*F+b*((A ((1-h)*s+h*u)-A s)/h))+μ*k*A s :=
      add_nonneg (sub_nonneg.mpr hCombined) hA
    _ = _ := by ring

/-- The full normalized head chart for both written G3 weight bands. -/
theorem g3_head_chart_gap {h σ p s : ℝ} (hh : 0<h) (hσ : 0<σ) (hσ₁ : σ≤1/5)
    (hh₁ : h≤1/(2-σ/(2-σ))) (hp : |p|≤1/8) (hs : |s|≤1/8) :
    0≤g3FacetGap h σ p s 1 := by
  by_cases ho : s≤-(σ/(2-σ)*(1-p))/2 ∨ σ/(2-σ)*(1-p)≤s
  · exact head_outside_middle hh hσ hσ₁ hh₁ hp hs ho
  · exact head_middle_gap hh hσ hσ₁ hh₁ hp hs
      (le_of_not_ge fun h => ho (Or.inl h)) (le_of_not_ge fun h => ho (Or.inr h))

end HlawkaSchatten.BelowExponent
