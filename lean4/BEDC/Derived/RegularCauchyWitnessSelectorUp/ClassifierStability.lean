import BEDC.Derived.RegularCauchyWitnessSelectorUp.TasteGate

namespace BEDC.Derived.RegularCauchyWitnessSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

theorem RegularCauchyWitnessSelector_classifier_stability
    {x y : RegularCauchyWitnessSelectorUp} :
    regularCauchyWitnessSelectorToEventFlow x =
        regularCauchyWitnessSelectorToEventFlow y ->
      x = y ∧
        ∃ prefixRows : List (List BMark),
          prefixRows = (regularCauchyWitnessSelectorToEventFlow x).take 4 ∧
            prefixRows = (regularCauchyWitnessSelectorToEventFlow y).take 4 := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have decode_encode :
      ∀ h : BHist,
        regularCauchyWitnessSelectorDecodeBHist
          (regularCauchyWitnessSelectorEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  have xy : x = y := by
    cases x with
    | mk modulusRequest₁ selectedWindow₁ tolerance₁ readback₁ sealRow₁ transport₁ route₁
        provenance₁ name₁ =>
        cases y with
        | mk modulusRequest₂ selectedWindow₂ tolerance₂ readback₂ sealRow₂ transport₂ route₂
            provenance₂ name₂ =>
            change
              [regularCauchyWitnessSelectorEncodeBHist modulusRequest₁,
                regularCauchyWitnessSelectorEncodeBHist selectedWindow₁,
                regularCauchyWitnessSelectorEncodeBHist tolerance₁,
                regularCauchyWitnessSelectorEncodeBHist readback₁,
                regularCauchyWitnessSelectorEncodeBHist sealRow₁,
                regularCauchyWitnessSelectorEncodeBHist transport₁,
                regularCauchyWitnessSelectorEncodeBHist route₁,
                regularCauchyWitnessSelectorEncodeBHist provenance₁,
                regularCauchyWitnessSelectorEncodeBHist name₁] =
              [regularCauchyWitnessSelectorEncodeBHist modulusRequest₂,
                regularCauchyWitnessSelectorEncodeBHist selectedWindow₂,
                regularCauchyWitnessSelectorEncodeBHist tolerance₂,
                regularCauchyWitnessSelectorEncodeBHist readback₂,
                regularCauchyWitnessSelectorEncodeBHist sealRow₂,
                regularCauchyWitnessSelectorEncodeBHist transport₂,
                regularCauchyWitnessSelectorEncodeBHist route₂,
                regularCauchyWitnessSelectorEncodeBHist provenance₂,
                regularCauchyWitnessSelectorEncodeBHist name₂] at heq
            injection heq with hModulusRequest t1
            injection t1 with hSelectedWindow t2
            injection t2 with hTolerance t3
            injection t3 with hReadback t4
            injection t4 with hSealRow t5
            injection t5 with hTransport t6
            injection t6 with hRoute t7
            injection t7 with hProvenance t8
            injection t8 with hName _
            have hModulusRequestRow : modulusRequest₁ = modulusRequest₂ := by
              have hdecode :=
                congrArg regularCauchyWitnessSelectorDecodeBHist hModulusRequest
              rw [decode_encode modulusRequest₁, decode_encode modulusRequest₂] at hdecode
              exact hdecode
            have hSelectedWindowRow : selectedWindow₁ = selectedWindow₂ := by
              have hdecode :=
                congrArg regularCauchyWitnessSelectorDecodeBHist hSelectedWindow
              rw [decode_encode selectedWindow₁, decode_encode selectedWindow₂] at hdecode
              exact hdecode
            have hToleranceRow : tolerance₁ = tolerance₂ := by
              have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hTolerance
              rw [decode_encode tolerance₁, decode_encode tolerance₂] at hdecode
              exact hdecode
            have hReadbackRow : readback₁ = readback₂ := by
              have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hReadback
              rw [decode_encode readback₁, decode_encode readback₂] at hdecode
              exact hdecode
            have hSealRowEq : sealRow₁ = sealRow₂ := by
              have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hSealRow
              rw [decode_encode sealRow₁, decode_encode sealRow₂] at hdecode
              exact hdecode
            have hTransportRow : transport₁ = transport₂ := by
              have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hTransport
              rw [decode_encode transport₁, decode_encode transport₂] at hdecode
              exact hdecode
            have hRouteRow : route₁ = route₂ := by
              have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hRoute
              rw [decode_encode route₁, decode_encode route₂] at hdecode
              exact hdecode
            have hProvenanceRow : provenance₁ = provenance₂ := by
              have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hProvenance
              rw [decode_encode provenance₁, decode_encode provenance₂] at hdecode
              exact hdecode
            have hNameRow : name₁ = name₂ := by
              have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hName
              rw [decode_encode name₁, decode_encode name₂] at hdecode
              exact hdecode
            cases hModulusRequestRow
            cases hSelectedWindowRow
            cases hToleranceRow
            cases hReadbackRow
            cases hSealRowEq
            cases hTransportRow
            cases hRouteRow
            cases hProvenanceRow
            cases hNameRow
            rfl
  constructor
  · exact xy
  · cases xy
    exact ⟨(regularCauchyWitnessSelectorToEventFlow x).take 4, rfl, rfl⟩

end BEDC.Derived.RegularCauchyWitnessSelectorUp
