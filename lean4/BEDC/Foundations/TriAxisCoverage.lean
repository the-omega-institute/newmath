import BEDC.Foundations.TriangleGenerationSystem

namespace BEDC.Foundations.TriAxisCoverage

open BEDC.Foundations.TriangleGenerationSystem

inductive CoversDistinction : TriAxisObjCode → Prop where
  | here (c : TriAxisObjCode) :
      CoversDistinction (TriAxisObjCode.distinctionGen c)
  | timeGen {c : TriAxisObjCode} :
      CoversDistinction c →
      CoversDistinction (TriAxisObjCode.timeGen c)
  | symmetryGen {c : TriAxisObjCode} :
      CoversDistinction c →
      CoversDistinction (TriAxisObjCode.symmetryGen c)
  | pairLeft {left right : TriAxisObjCode} :
      CoversDistinction left →
      CoversDistinction (TriAxisObjCode.pairGen left right)
  | pairRight {left right : TriAxisObjCode} :
      CoversDistinction right →
      CoversDistinction (TriAxisObjCode.pairGen left right)

inductive CoversTime : TriAxisObjCode → Prop where
  | here (c : TriAxisObjCode) :
      CoversTime (TriAxisObjCode.timeGen c)
  | distinctionGen {c : TriAxisObjCode} :
      CoversTime c →
      CoversTime (TriAxisObjCode.distinctionGen c)
  | symmetryGen {c : TriAxisObjCode} :
      CoversTime c →
      CoversTime (TriAxisObjCode.symmetryGen c)
  | pairLeft {left right : TriAxisObjCode} :
      CoversTime left →
      CoversTime (TriAxisObjCode.pairGen left right)
  | pairRight {left right : TriAxisObjCode} :
      CoversTime right →
      CoversTime (TriAxisObjCode.pairGen left right)

inductive CoversSymmetry : TriAxisObjCode → Prop where
  | here (c : TriAxisObjCode) :
      CoversSymmetry (TriAxisObjCode.symmetryGen c)
  | distinctionGen {c : TriAxisObjCode} :
      CoversSymmetry c →
      CoversSymmetry (TriAxisObjCode.distinctionGen c)
  | timeGen {c : TriAxisObjCode} :
      CoversSymmetry c →
      CoversSymmetry (TriAxisObjCode.timeGen c)
  | pairLeft {left right : TriAxisObjCode} :
      CoversSymmetry left →
      CoversSymmetry (TriAxisObjCode.pairGen left right)
  | pairRight {left right : TriAxisObjCode} :
      CoversSymmetry right →
      CoversSymmetry (TriAxisObjCode.pairGen left right)

theorem base_not_covers_distinction :
    CoversDistinction TriAxisObjCode.base → False := by
  intro h
  cases h

theorem base_not_covers_time :
    CoversTime TriAxisObjCode.base → False := by
  intro h
  cases h

theorem base_not_covers_symmetry :
    CoversSymmetry TriAxisObjCode.base → False := by
  intro h
  cases h

inductive AxisDemand : Type where
  | distinctionOnly
  | timeOnly
  | symmetryOnly
  | distinctionTime
  | distinctionSymmetry
  | timeSymmetry
  | allThree

def AxisDemand.Covers : AxisDemand → TriAxisObjCode → Prop
  | AxisDemand.distinctionOnly, code => CoversDistinction code
  | AxisDemand.timeOnly, code => CoversTime code
  | AxisDemand.symmetryOnly, code => CoversSymmetry code
  | AxisDemand.distinctionTime, code =>
      CoversDistinction code ∧ CoversTime code
  | AxisDemand.distinctionSymmetry, code =>
      CoversDistinction code ∧ CoversSymmetry code
  | AxisDemand.timeSymmetry, code =>
      CoversTime code ∧ CoversSymmetry code
  | AxisDemand.allThree, code =>
      CoversDistinction code ∧ CoversTime code ∧ CoversSymmetry code

theorem base_not_covers_axis_demand
    (demand : AxisDemand) :
    AxisDemand.Covers demand TriAxisObjCode.base → False := by
  cases demand <;> intro h
  · exact base_not_covers_distinction h
  · exact base_not_covers_time h
  · exact base_not_covers_symmetry h
  · exact base_not_covers_distinction h.left
  · exact base_not_covers_distinction h.left
  · exact base_not_covers_time h.left
  · exact base_not_covers_distinction h.left

class TriAxisProjected (α : Type u) where
  code : TriAxisObjCode
  projection_forced : ExistsUniqueProjection code
  demanded_axes : AxisDemand
  covers_some : AxisDemand.Covers demanded_axes code

theorem triAxisProjected_base_code_excluded
    (α : Type u) [TriAxisProjected α]
    (hCode : TriAxisProjected.code (α := α) = TriAxisObjCode.base) :
    False := by
  have hCovers :
      AxisDemand.Covers
        (TriAxisProjected.demanded_axes (α := α))
        (TriAxisProjected.code (α := α)) :=
    TriAxisProjected.covers_some (α := α)
  have hBaseCovers :
      AxisDemand.Covers
        (TriAxisProjected.demanded_axes (α := α))
        TriAxisObjCode.base := by
    rw [← hCode]
    exact hCovers
  exact
    base_not_covers_axis_demand
      (TriAxisProjected.demanded_axes (α := α))
      hBaseCovers

structure TriAxisBindingObligation (α : Type u) where
  proposed_code : TriAxisObjCode
  projection_forced : ExistsUniqueProjection proposed_code
  demanded_axes : AxisDemand
  covers_some : AxisDemand.Covers demanded_axes proposed_code

def natTypeObjCode : TriAxisObjCode :=
  TriAxisObjCode.pairGen
    (TriAxisObjCode.distinctionGen TriAxisObjCode.base)
    (TriAxisObjCode.timeGen TriAxisObjCode.base)

theorem natTypeObjCode_covers_distinction :
    CoversDistinction natTypeObjCode := by
  unfold natTypeObjCode
  exact CoversDistinction.pairLeft
    (CoversDistinction.here TriAxisObjCode.base)

theorem natTypeObjCode_covers_time :
    CoversTime natTypeObjCode := by
  unfold natTypeObjCode
  exact CoversTime.pairRight
    (CoversTime.here TriAxisObjCode.base)

instance natTriAxisProjected : TriAxisProjected Nat where
  code := natTypeObjCode
  projection_forced := triAxisProjection_forced_unique natTypeObjCode
  demanded_axes := AxisDemand.distinctionTime
  covers_some := ⟨natTypeObjCode_covers_distinction, natTypeObjCode_covers_time⟩

def signedIntTypeObjCode : TriAxisObjCode :=
  TriAxisObjCode.pairGen
    natTypeObjCode
    (TriAxisObjCode.symmetryGen TriAxisObjCode.base)

theorem signedIntTypeObjCode_covers_distinction :
    CoversDistinction signedIntTypeObjCode := by
  unfold signedIntTypeObjCode
  exact CoversDistinction.pairLeft natTypeObjCode_covers_distinction

theorem signedIntTypeObjCode_covers_time :
    CoversTime signedIntTypeObjCode := by
  unfold signedIntTypeObjCode
  exact CoversTime.pairLeft natTypeObjCode_covers_time

theorem signedIntTypeObjCode_covers_symmetry :
    CoversSymmetry signedIntTypeObjCode := by
  unfold signedIntTypeObjCode
  exact CoversSymmetry.pairRight
    (CoversSymmetry.here TriAxisObjCode.base)

instance signedIntCodeTriAxisProjected :
    TriAxisProjected SignedIntCode where
  code := signedIntTypeObjCode
  projection_forced := triAxisProjection_forced_unique signedIntTypeObjCode
  demanded_axes := AxisDemand.allThree
  covers_some :=
    ⟨signedIntTypeObjCode_covers_distinction,
      signedIntTypeObjCode_covers_time,
      signedIntTypeObjCode_covers_symmetry⟩

instance intTriAxisProjected : TriAxisProjected Int where
  code := signedIntTypeObjCode
  projection_forced := triAxisProjection_forced_unique signedIntTypeObjCode
  demanded_axes := AxisDemand.allThree
  covers_some :=
    ⟨signedIntTypeObjCode_covers_distinction,
      signedIntTypeObjCode_covers_time,
      signedIntTypeObjCode_covers_symmetry⟩

end BEDC.Foundations.TriAxisCoverage
