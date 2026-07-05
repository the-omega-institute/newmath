import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyScalarUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyScalarCarrier [AskSetup] [PackageSetup]
    (source scalar window sourceObservation scaledLedger realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  UnaryHistory source ∧ UnaryHistory scalar ∧ UnaryHistory window ∧
    UnaryHistory sourceObservation ∧ UnaryHistory scaledLedger ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont window source sourceObservation ∧
          Cont sourceObservation scalar scaledLedger ∧ Cont scaledLedger replay realSeal ∧
            hsame transport (append scaledLedger replay) ∧ PkgSig bundle provenance pkg

theorem RegularCauchyScalarRealHandoff [AskSetup] [PackageSetup]
    {X A W D F E H C P N sourceRead scaledRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScalarCarrier X A W D F E H C P N bundle pkg ->
      Cont X W sourceRead ->
        Cont sourceRead F scaledRead ->
          Cont scaledRead E realRead ->
            PkgSig bundle realRead pkg ->
              UnaryHistory X ∧ UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory F ∧
                UnaryHistory E ∧ UnaryHistory sourceRead ∧ UnaryHistory scaledRead ∧
                  UnaryHistory realRead ∧ Cont X W sourceRead ∧ Cont sourceRead F scaledRead ∧
                    Cont scaledRead E realRead ∧ hsame H (append F C) ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier sourceCont scaledCont realCont realPkg
  rcases carrier with
    ⟨unaryX, unaryA, unaryW, _unaryD, unaryF, unaryE, _unaryH, _unaryC, unaryP,
      _unaryN, _windowSourceObservation, _observationScalarScaled, _scaledReplayReal,
      sameTransport, provenancePkg⟩
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryX unaryW sourceCont
  have scaledReadUnary : UnaryHistory scaledRead :=
    unary_cont_closed sourceReadUnary unaryF scaledCont
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed scaledReadUnary unaryE realCont
  exact
    ⟨unaryX, unaryA, unaryW, unaryF, unaryE, sourceReadUnary, scaledReadUnary,
      realReadUnary, sourceCont, scaledCont, realCont, sameTransport, provenancePkg, realPkg⟩

theorem RegularCauchyScalarCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X A W D F E H C P N sourceRead scaledRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScalarCarrier X A W D F E H C P N bundle pkg ->
      Cont X W sourceRead ->
        Cont sourceRead F scaledRead ->
          Cont scaledRead E realRead ->
            PkgSig bundle realRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  (hsame row X ∨ hsame row A ∨ hsame row W ∨ hsame row D ∨
                      hsame row F ∨ hsame row E ∨ hsame row realRead) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row X ∨ hsame row A ∨ hsame row W ∨ hsame row D ∨
                    hsame row F ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                      hsame row P ∨ hsame row N ∨ hsame row realRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont X W sourceRead ∧ Cont sourceRead F scaledRead ∧
                    Cont scaledRead E realRead ∧ PkgSig bundle realRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier sourceCont scaledCont realCont realPkg
  rcases carrier with
    ⟨unaryX, unaryA, unaryW, unaryD, unaryF, unaryE, _unaryH, _unaryC, _unaryP,
      _unaryN, _windowSourceObservation, _observationScalarScaled, _scaledReplayReal,
      _sameTransport, _provenancePkg⟩
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryX unaryW sourceCont
  have scaledReadUnary : UnaryHistory scaledRead :=
    unary_cont_closed sourceReadUnary unaryF scaledCont
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed scaledReadUnary unaryE realCont
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro realRead
          ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl realRead)))))),
            realReadUnary⟩
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
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      rcases sourceRow with ⟨sourceCases, _sourceUnary⟩
      rcases sourceCases with xRow | aRow | wRow | dRow | fRow | eRow | realRow
      · exact Or.inl xRow
      · exact Or.inr (Or.inl aRow)
      · exact Or.inr (Or.inr (Or.inl wRow))
      · exact Or.inr (Or.inr (Or.inr (Or.inl dRow)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl fRow))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eRow)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr realRow)))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, sourceCont, scaledCont, realCont, realPkg⟩
  }

theorem RegularCauchyScalarCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {X A W D F E H C P N sourceRead scaledRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScalarCarrier X A W D F E H C P N bundle pkg ->
      Cont X W sourceRead ->
        Cont sourceRead F scaledRead ->
          Cont scaledRead E realRead ->
            PkgSig bundle realRead pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row realRead ∧ Cont X W sourceRead ∧
                        Cont sourceRead F scaledRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont scaledRead E realRead ∧
                        hsame H (append F C) ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle realRead pkg)
                    hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory scaledRead ∧
                  UnaryHistory realRead ∧ hsame H (append F C) ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier sourceCont scaledCont realCont realPkg
  have handoff :=
    RegularCauchyScalarRealHandoff carrier sourceCont scaledCont realCont realPkg
  rcases carrier with
    ⟨_unaryX, _unaryA, _unaryW, _unaryD, _unaryF, _unaryE, _unaryH, _unaryC,
      _unaryP, _unaryN, _windowSourceObservation, _observationScalarScaled,
      _scaledReplayReal, sameTransport, provenancePkg⟩
  rcases handoff with
    ⟨_unaryX, _unaryA, _unaryW, _unaryF, _unaryE, sourceReadUnary,
      scaledReadUnary, realReadUnary, _sourceRoute, _scaledRoute, _realRoute,
      sameRouteTransport, provenancePkg', realPkg'⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row realRead ∧ Cont X W sourceRead ∧ Cont sourceRead F scaledRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont scaledRead E realRead ∧ hsame H (append F C) ∧
              PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, sourceCont, scaledCont⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realCont, sameRouteTransport, provenancePkg', realPkg'⟩
  }
  exact
    ⟨cert, sourceReadUnary, scaledReadUnary, realReadUnary, sameTransport, provenancePkg,
      realPkg⟩

theorem RegularCauchyScalar_scoped_consumer_route [AskSetup] [PackageSetup]
    {X A W D F E H C P N sourceRead scaledRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScalarCarrier X A W D F E H C P N bundle pkg →
      Cont X W sourceRead →
        Cont sourceRead F scaledRead →
          Cont scaledRead E realRead →
            PkgSig bundle realRead pkg →
              SemanticNameCert
                    (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row realRead ∧ Cont X W sourceRead ∧
                        Cont sourceRead F scaledRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont scaledRead E realRead ∧
                        hsame H (append F C) ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle realRead pkg)
                    hsame ∧
                  SemanticNameCert
                    (fun row : BHist =>
                      (hsame row X ∨ hsame row A ∨ hsame row W ∨ hsame row D ∨
                          hsame row F ∨ hsame row E ∨ hsame row realRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row A ∨ hsame row W ∨ hsame row D ∨
                        hsame row F ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row realRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont X W sourceRead ∧
                        Cont sourceRead F scaledRead ∧ Cont scaledRead E realRead ∧
                          PkgSig bundle realRead pkg)
                    hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory scaledRead ∧
                  UnaryHistory realRead ∧ hsame H (append F C) ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier sourceCont scaledCont realCont realPkg
  have closurePackage :=
    RegularCauchyScalarCarrier_obligation_closure_package (X := X) (A := A) (W := W)
      (D := D) (F := F) (E := E) (H := H) (C := C) (P := P) (N := N)
      (sourceRead := sourceRead) (scaledRead := scaledRead) (realRead := realRead)
      (bundle := bundle) (pkg := pkg) carrier sourceCont scaledCont realCont realPkg
  have namecertObligations :=
    RegularCauchyScalarCarrier_namecert_obligations (X := X) (A := A) (W := W)
      (D := D) (F := F) (E := E) (H := H) (C := C) (P := P) (N := N)
      (sourceRead := sourceRead) (scaledRead := scaledRead) (realRead := realRead)
      (bundle := bundle) (pkg := pkg) carrier sourceCont scaledCont realCont realPkg
  rcases closurePackage with
    ⟨consumerCert, sourceReadUnary, scaledReadUnary, realReadUnary, sameTransport,
      provenancePkg, realPkg'⟩
  exact
    ⟨consumerCert, namecertObligations, sourceReadUnary, scaledReadUnary, realReadUnary,
      sameTransport, provenancePkg, realPkg'⟩

end BEDC.Derived.RegularCauchyScalarUp
