module
public import Glennie.Compact.SharpPolarizationR01
public import Glennie.Covariance

/- Input displacement using the native raw trace norm. -/
@[expose] public section
namespace Glennie.Compact.NativeNormKernel
open Glennie
noncomputable section
set_option autoImplicit false

 def F (x y z : Albert) : Albert := U x (U y z) - U y (U x z)
 def H (x y z : Albert) : Albert := U z (jordan x y)

 theorem U_norm_radius (x w : Albert) (R : ℝ) (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) :
    ‖U x w‖ ≤ R^2 * ‖w‖ := by
  calc
    _ ≤ ‖x‖^2 * ‖w‖ := U_norm _ _
    _ ≤ R^2 * ‖w‖ := by gcongr

 theorem U_norm_radius_input (x w : Albert) (R S : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hw : ‖w‖ ≤ S) : ‖U x w‖ ≤ R^2*S := by
  exact (U_norm_radius x w R hR hx).trans
    (mul_le_mul_of_nonneg_left hw (sq_nonneg R))

 theorem F_norm_radius (x y z : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖F x y z‖ ≤ 2*R^5 := by
  calc
    _ ≤ ‖U x (U y z)‖ + ‖U y (U x z)‖ := norm_sub_le _ _
    _ ≤ R^2 * (R^2 * R) + R^2 * (R^2 * R) := by
      exact add_le_add
        (U_norm_radius_input x (U y z) R (R^2*R) hR hx
          (U_norm_radius_input y z R R hR hy hz))
        (U_norm_radius_input y (U x z) R (R^2*R) hR hy
          (U_norm_radius_input x z R R hR hx hz))
    _ = 2*R^5 := by ring

 theorem H_norm_radius (x y z : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖H x y z‖ ≤ R^4 := by
  calc
    _ ≤ R^2 * ‖jordan x y‖ := U_norm_radius _ _ _ hR hz
    _ ≤ R^2 * (‖x‖*‖y‖) := by gcongr; exact jordan_norm _ _
    _ ≤ R^2 * (R*R) := by gcongr
    _ = R^4 := by ring

 theorem F_sub_first (x x' y z : Albert) :
    F x y z - F x' y z =
      (U x (U y z) - U x' (U y z)) - U y (U x z - U x' z) := by
  simp only [F, U_sub_argument]
  abel

 theorem F_sub_first_radius (x x' y z : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hx' : ‖x'‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖F x y z-F x' y z‖ ≤ 4*R^4*‖x-x'‖ := by
  rw [F_sub_first]
  calc
    _ ≤ ‖U x (U y z)-U x' (U y z)‖ + ‖U y (U x z-U x' z)‖ := norm_sub_le _ _
    _ ≤ (2*R*‖x-x'‖)*‖U y z‖ + R^2 * ‖U x z-U x' z‖ := by
      exact add_le_add (U_sub_base_radius _ _ _ _ hx hx')
        (U_norm_radius _ _ _ hR hy)
    _ ≤ (2*R*‖x-x'‖)*(R^2*R) + R^2*((2*R*‖x-x'‖)*R) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (U_norm_radius_input y z R R hR hy hz) (by positivity)
      · apply mul_le_mul_of_nonneg_left _ (sq_nonneg R)
        exact (U_sub_base_radius x x' z R hx hx').trans
          (mul_le_mul_of_nonneg_left hz (by positivity))
    _ = 4*R^4*‖x-x'‖ := by ring

 theorem H_sub_first_radius (x x' y z : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖H x y z-H x' y z‖ ≤ R^3*‖x-x'‖ := by
  have he : H x y z-H x' y z = U z (jordan (x-x') y) := by
    simp only [H, jordan_sub_left, U_sub_argument]
  rw [he]
  calc
    _ ≤ R^2*‖jordan (x-x') y‖ := U_norm_radius _ _ _ hR hz
    _ ≤ R^2*(‖x-x'‖*‖y‖) := by gcongr; exact jordan_norm _ _
    _ ≤ R^2*(‖x-x'‖*R) := by gcongr
    _ = R^3*‖x-x'‖ := by ring

 theorem pairing_difference (a b a' b' : Albert) :
    |inner a b-inner a' b'| ≤ ‖a-a'‖*‖b‖ + ‖a'‖*‖b-b'‖ := by
  have he : inner a b-inner a' b' = inner (a-a') b + inner a' (b-b') := by
    simp only [inner_sub_left,inner_sub_right]; ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (native_cauchy _ _) (native_cauchy _ _))

 theorem phi_sub_first_radius (x x' y z : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hx' : ‖x'‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |phi x y z-phi x' y z| ≤ 6*R^8*‖x-x'‖ := by
  change |inner (F x y z) (H x y z)-inner (F x' y z) (H x' y z)| ≤ _
  calc
    _ ≤ ‖F x y z-F x' y z‖*‖H x y z‖ + ‖F x' y z‖*‖H x y z-H x' y z‖ :=
      pairing_difference _ _ _ _
    _ ≤ (4*R^4*‖x-x'‖)*R^4 + (2*R^5)*(R^3*‖x-x'‖) := by
      gcongr
      · exact F_sub_first_radius _ _ _ _ _ hR hx hx' hy hz
      · exact H_norm_radius _ _ _ _ hR hx hy hz
      · exact F_norm_radius _ _ _ _ hR hx' hy hz
      · exact H_sub_first_radius _ _ _ _ _ hR hy hz
    _ = 6*R^8*‖x-x'‖ := by ring

 theorem phi_sub_second_radius (x y y' z : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |phi x y z-phi x y' z| ≤ 6*R^8*‖y-y'‖ := by
  have he : phi x y z-phi x y' z = -(phi y x z-phi y' x z) := by
    rw [phi_swap_first_two y x, phi_swap_first_two y' x]; ring
  rw [he, abs_neg]
  exact phi_sub_first_radius _ _ _ _ _ hR hy hy' hx hz

 theorem phi_sub_third_radius (x y z z' : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) (hz' : ‖z'‖ ≤ R) :
    |phi x y z-phi x y z'| ≤ 6*R^8*‖z-z'‖ := by
  have he : phi x y z-phi x y z' = -(phi z y x-phi z' y x) := by
    rw [phi_swap_first_third z y x, phi_swap_first_third z' y x]; ring
  rw [he, abs_neg]
  exact phi_sub_first_radius _ _ _ _ _ hR hz hz' hy hx

 theorem phi_displacement_sum (x y z x' y' z' : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hx' : ‖x'‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz' : ‖z'‖ ≤ R) :
    |phi x y z-phi x' y' z'| ≤
      6*R^8*(‖x-x'‖+‖y-y'‖+‖z-z'‖) := by
  have he : phi x y z-phi x' y' z' =
      (phi x y z-phi x' y z) + (phi x' y z-phi x' y' z) +
      (phi x' y' z-phi x' y' z') := by ring
  rw [he]
  calc
    _ ≤ |phi x y z-phi x' y z| + |phi x' y z-phi x' y' z| +
      |phi x' y' z-phi x' y' z'| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ 6*R^8*‖x-x'‖ + 6*R^8*‖y-y'‖ + 6*R^8*‖z-z'‖ := by
      exact add_le_add (add_le_add
        (phi_sub_first_radius _ _ _ _ _ hR hx hx' hy hz)
        (phi_sub_second_radius _ _ _ _ _ hR hx' hy hy' hz))
        (phi_sub_third_radius _ _ _ _ _ hR hx' hy' hz hz')
    _ = _ := by ring

 theorem phi_displacement_18 (x y z x' y' z' : Albert) (R δ : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hx' : ‖x'‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (hdx : ‖x-x'‖ ≤ δ) (hdy : ‖y-y'‖ ≤ δ) (hdz : ‖z-z'‖ ≤ δ) :
    |phi x y z-phi x' y' z'| ≤ 18*R^8*δ := by
  calc
    _ ≤ 6*R^8*(‖x-x'‖+‖y-y'‖+‖z-z'‖) :=
      phi_displacement_sum _ _ _ _ _ _ _ hR hx hy hz hx' hy' hz'
    _ ≤ 6*R^8*(δ+δ+δ) := by gcongr
    _ = 18*R^8*δ := by ring

 theorem phi_displacement_max (x y z x' y' z' : Albert) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hx' : ‖x'‖ ≤ R) (hy' : ‖y'‖ ≤ R) (hz' : ‖z'‖ ≤ R) :
    |phi x y z-phi x' y' z'| ≤
      18*R^8*max ‖x-x'‖ (max ‖y-y'‖ ‖z-z'‖) := by
  apply phi_displacement_18 _ _ _ _ _ _ _ _ hR hx hy hz hx' hy' hz'
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

end
end Glennie.Compact.NativeNormKernel
