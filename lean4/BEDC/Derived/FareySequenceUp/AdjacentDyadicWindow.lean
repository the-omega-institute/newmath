import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceAdjacentDyadicWindow [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N adjacentRead mediantRead dyadicRead
      streamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A adjacentRead ->
        Cont adjacentRead M mediantRead ->
          Cont T Q dyadicRead ->
            Cont Q W streamRead ->
              PkgSig bundle streamRead pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    (hsame row dyadicRead ∨ hsame row streamRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
                      hsame row T ∨ hsame row Q ∨ hsame row W ∨
                        hsame row dyadicRead ∨ hsame row streamRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle streamRead pkg)
                  hsame ∧
                    UnaryHistory adjacentRead ∧ UnaryHistory mediantRead ∧
                      UnaryHistory dyadicRead ∧ UnaryHistory streamRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier adjacentRoute mediantRoute dyadicRoute streamRoute streamPkg
  obtain ⟨unaryB, unaryA, unaryM, _unaryL, unaryT, _unaryS, _unaryD, unaryQ,
    unaryW, _unaryR, _unaryG, _unaryE, _unaryH, _unaryC, _unaryP, _unaryN,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, provenancePkg⟩ := carrier
  have adjacentUnary : UnaryHistory adjacentRead :=
    unary_cont_closed unaryB unaryA adjacentRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed adjacentUnary unaryM mediantRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed unaryT unaryQ dyadicRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed unaryQ unaryW streamRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          (hsame row dyadicRead ∨ hsame row streamRead) ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
            hsame row T ∨ hsame row Q ∨ hsame row W ∨
              hsame row dyadicRead ∨ hsame row streamRead)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle streamRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dyadicRead ⟨Or.inl (hsame_refl dyadicRead), dyadicUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        constructor
        · cases source.left with
          | inl sameDyadic =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic)
          | inr sameStream =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameStream)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameDyadic =>
          right
          right
          right
          right
          right
          right
          right
          left
          exact sameDyadic
      | inr sameStream =>
          right
          right
          right
          right
          right
          right
          right
          right
          exact sameStream
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, streamPkg⟩
  }
  exact ⟨cert, adjacentUnary, mediantUnary, dyadicUnary, streamUnary⟩

end BEDC.Derived.FareySequenceUp
