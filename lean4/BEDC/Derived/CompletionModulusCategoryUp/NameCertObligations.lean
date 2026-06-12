import BEDC.Derived.CompletionModulusCategoryUp.ModulusFunctoriality

namespace BEDC.Derived.CompletionModulusCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompletionModulusCategoryCarrier [AskSetup] [PackageSetup]
    (O A S R D E F H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: CompletionModulusCategoryUp BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧
    UnaryHistory E ∧ UnaryHistory F ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CompletionModulusCategoryNameCertObligations [AskSetup] [PackageSetup]
    {O A S R D E F H C P N objectRead toleranceRead functorRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionModulusCategoryCarrier O A S R D E F H C P N bundle pkg →
      Cont O A objectRead →
        Cont S R toleranceRead →
          Cont toleranceRead D functorRead →
            Cont functorRead F replayRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row O ∨ hsame row A ∨ hsame row S ∨ hsame row R ∨
                          hsame row D ∨ hsame row E ∨ hsame row F ∨ hsame row H ∨
                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                              hsame row objectRead ∨ hsame row toleranceRead ∨
                                hsame row functorRead ∨ hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont O A objectRead ∧ Cont S R toleranceRead ∧
                          Cont toleranceRead D functorRead ∧ Cont functorRead F replayRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                      hsame := by
  -- BEDC touchpoint anchor: CompletionModulusCategoryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier objectRoute toleranceRoute functorRoute replayRoute provenancePkg namePkg
  obtain ⟨unaryO, unaryA, unaryS, unaryR, unaryD, _unaryE, unaryF, _unaryH, _unaryC,
    _unaryP, _unaryN, _carrierPkgP, _carrierPkgN⟩ := carrier
  exact
    (CompletionModulusCategoryModulusFunctoriality
      (O := O) (A := A) (S := S) (R := R) (D := D) (E := E) (F := F) (H := H)
      (C := C) (P := P) (N := N) (objectRead := objectRead)
      (toleranceRead := toleranceRead) (functorRead := functorRead)
      (replayRead := replayRead) (bundle := bundle) (pkg := pkg)
      unaryO unaryA unaryS unaryR unaryD _unaryE unaryF _unaryH _unaryC _unaryP _unaryN
      objectRoute toleranceRoute functorRoute replayRoute provenancePkg namePkg).left

end BEDC.Derived.CompletionModulusCategoryUp
