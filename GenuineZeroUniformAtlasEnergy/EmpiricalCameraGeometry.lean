import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-!
# Geometry of the empirical six-camera stack

The cutoff experiments use six camera labels, `2, 3, 4, 5, 6, 7`.  A label
is not always the period: the camera labelled `2` has period `4`.  The exact
period table is

```text
label   2  3  4  5  6  7
period  4  3  4  5  6  7
```

The retained positive radii are `1, ..., floor(label / 2)`.  In particular,
the even cameras labelled `4` and `6` retain their antipodal radii `2` and
`3`.  This is the empirical all-bases convention; no identification is made
here with an even natural camera that omits its middle channel.

The finite type below is intended to be the index type for later camera
vectors, cutoff tails, and collective quadratic energies.  All table entries
and the second radius moments are proved by finite kernel-checked reductions.
-/

open scoped BigOperators

namespace GenuineZeroUniformAtlasEnergy

/-- The six camera labels used by the empirical cutoff operator. -/
inductive EmpiricalCamera
  | c2
  | c3
  | c4
  | c5
  | c6
  | c7
  deriving DecidableEq, Fintype, Repr

namespace EmpiricalCamera

/-- Numerical label attached to an empirical camera. -/
@[simp] def label : EmpiricalCamera → ℕ
  | c2 => 2
  | c3 => 3
  | c4 => 4
  | c5 => 5
  | c6 => 6
  | c7 => 7

/-- Period used by the finite operator.  The `c2` camera has period four. -/
@[simp] def period : EmpiricalCamera → ℕ
  | c2 => 4
  | c3 => 3
  | c4 => 4
  | c5 => 5
  | c6 => 6
  | c7 => 7

/-- Retained positive radii, including the even antipodal endpoint. -/
@[simp] def radii : EmpiricalCamera → Finset ℕ
  | c2 => {1}
  | c3 => {1}
  | c4 => {1, 2}
  | c5 => {1, 2}
  | c6 => {1, 2, 3}
  | c7 => {1, 2, 3}

/-- The second radius moment `S2 = sum_{r in R} r^2`. -/
def secondRadiusMoment (camera : EmpiricalCamera) : ℕ :=
  ∑ radius ∈ radii camera, radius ^ 2

/-- The exact rational geometry factor occurring in the squared leading tail. -/
def leadingTailGeometryWeight (camera : EmpiricalCamera) : ℚ :=
  ((secondRadiusMoment camera : ℚ) ^ 2) /
    ((period camera : ℚ) ^ 5)

/-- The label map identifies the six constructors without collisions. -/
theorem label_injective : Function.Injective label := by
  intro camera other h
  cases camera <;> cases other <;> simp_all

/-- Every empirical label lies in the exact interval from two through seven. -/
theorem label_mem_Icc (camera : EmpiricalCamera) :
    label camera ∈ Finset.Icc 2 7 := by
  cases camera <;> norm_num

/-- The complete finite label set is exactly `{2, 3, 4, 5, 6, 7}`. -/
theorem image_label_univ_eq_Icc :
    Finset.univ.image label = Finset.Icc 2 7 := by
  decide

/-- There are exactly six empirical cameras. -/
@[simp] theorem card_univ : (Finset.univ : Finset EmpiricalCamera).card = 6 := by
  decide

/-- Kernel-checked period table `(4, 3, 4, 5, 6, 7)`. -/
theorem period_table :
    period c2 = 4 ∧ period c3 = 3 ∧ period c4 = 4 ∧
      period c5 = 5 ∧ period c6 = 6 ∧ period c7 = 7 := by
  norm_num

/-- Kernel-checked radius table, with the even antipodal endpoints retained. -/
theorem radii_table :
    radii c2 = {1} ∧ radii c3 = {1} ∧ radii c4 = {1, 2} ∧
      radii c5 = {1, 2} ∧ radii c6 = {1, 2, 3} ∧
        radii c7 = {1, 2, 3} := by
  norm_num

/-- Membership in the stored radius table has the uniform floor description. -/
theorem mem_radii_iff (camera : EmpiricalCamera) (radius : ℕ) :
    radius ∈ radii camera ↔
      1 ≤ radius ∧ radius ≤ label camera / 2 := by
  cases camera <;> simp <;> omega

/-- The explicit tables agree with `Icc 1 floor(label/2)`. -/
theorem radii_eq_Icc (camera : EmpiricalCamera) :
    radii camera = Finset.Icc 1 (label camera / 2) := by
  ext radius
  simpa using mem_radii_iff camera radius

/-- Every retained radius is positive and fits inside half of its label. -/
theorem radius_geometry
    (camera : EmpiricalCamera) {radius : ℕ}
    (hradius : radius ∈ radii camera) :
    1 ≤ radius ∧ 2 * radius ≤ label camera := by
  cases camera <;> simp_all <;> omega

/-- Every retained radius is strictly smaller than the operator period. -/
theorem radius_lt_period
    (camera : EmpiricalCamera) {radius : ℕ}
    (hradius : radius ∈ radii camera) :
    radius < period camera := by
  cases camera <;> simp_all <;> omega

/-- A camera has an antipodal channel when a retained radius is half its
operator period. -/
def HasAntipodalRadius (camera : EmpiricalCamera) : Prop :=
  ∃ radius ∈ radii camera, 2 * radius = period camera

/-- Precisely the empirical cameras labelled `4` and `6` retain an antipodal
channel.  The period-four `c2` camera retains only radius one. -/
theorem hasAntipodalRadius_iff (camera : EmpiricalCamera) :
    HasAntipodalRadius camera ↔ camera = c4 ∨ camera = c6 := by
  cases camera <;> simp [HasAntipodalRadius]

/-- The antipodal channel of the camera labelled four is radius two. -/
theorem c4_antipodal_radius :
    2 ∈ radii c4 ∧ 2 * 2 = period c4 := by
  norm_num

/-- The antipodal channel of the camera labelled six is radius three. -/
theorem c6_antipodal_radius :
    3 ∈ radii c6 ∧ 2 * 3 = period c6 := by
  norm_num

@[simp] theorem secondRadiusMoment_c2 : secondRadiusMoment c2 = 1 := by
  norm_num [secondRadiusMoment]

@[simp] theorem secondRadiusMoment_c3 : secondRadiusMoment c3 = 1 := by
  norm_num [secondRadiusMoment]

@[simp] theorem secondRadiusMoment_c4 : secondRadiusMoment c4 = 5 := by
  norm_num [secondRadiusMoment]

@[simp] theorem secondRadiusMoment_c5 : secondRadiusMoment c5 = 5 := by
  norm_num [secondRadiusMoment]

@[simp] theorem secondRadiusMoment_c6 : secondRadiusMoment c6 = 14 := by
  norm_num [secondRadiusMoment]

@[simp] theorem secondRadiusMoment_c7 : secondRadiusMoment c7 = 14 := by
  norm_num [secondRadiusMoment]

/-- The six second radius moments are exactly `(1, 1, 5, 5, 14, 14)`. -/
theorem secondRadiusMoment_table (camera : EmpiricalCamera) :
    secondRadiusMoment camera =
      match camera with
      | c2 => 1
      | c3 => 1
      | c4 => 5
      | c5 => 5
      | c6 => 14
      | c7 => 14 := by
  cases camera <;> simp

/-- The sum of the six second radius moments is forty. -/
theorem sum_secondRadiusMoment :
    (∑ camera : EmpiricalCamera, secondRadiusMoment camera) = 40 := by
  decide

/-- Exact collective geometry coefficient
`sum_camera S2(camera)^2 / period(camera)^5`. -/
theorem sum_leadingTailGeometryWeight :
    (∑ camera : EmpiricalCamera, leadingTailGeometryWeight camera) =
      (132244271 : ℚ) / 1778112000 := by
  change
    leadingTailGeometryWeight c2 +
      (leadingTailGeometryWeight c3 +
        (leadingTailGeometryWeight c4 +
          (leadingTailGeometryWeight c5 +
            (leadingTailGeometryWeight c6 +
              (leadingTailGeometryWeight c7 + 0))))) = _
  norm_num [leadingTailGeometryWeight]

end EmpiricalCamera

end GenuineZeroUniformAtlasEnergy
