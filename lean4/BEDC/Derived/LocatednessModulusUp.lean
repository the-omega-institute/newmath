import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatednessModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatednessModulusCarrier [AskSetup] [PackageSetup]
    (request locatedInterval rationalCells dyadicRows streamWindow readback realSeal transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory request ∧ UnaryHistory locatedInterval ∧ UnaryHistory rationalCells ∧
    UnaryHistory dyadicRows ∧ UnaryHistory streamWindow ∧ UnaryHistory readback ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem LocatednessModulusObligationWindowDecisionBudget [AskSetup] [PackageSetup]
    {request locatedInterval rationalCells dyadicRows streamWindow readback realSeal transport
      replay provenance localName cellRead dyadicRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatednessModulusCarrier request locatedInterval rationalCells dyadicRows streamWindow
        readback realSeal transport replay provenance localName bundle pkg →
      Cont request locatedInterval cellRead →
        Cont cellRead dyadicRows dyadicRead →
          Cont dyadicRead streamWindow windowRead →
            Cont windowRead realSeal sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row request ∨ hsame row locatedInterval ∨ hsame row dyadicRows ∨
                        hsame row streamWindow ∨ hsame row realSeal ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont request locatedInterval cellRead ∧
                        Cont cellRead dyadicRows dyadicRead ∧
                          Cont dyadicRead streamWindow windowRead ∧
                            Cont windowRead realSeal sealRead ∧ PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory dyadicRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier requestLocated cellDyadic dyadicWindow windowSeal sealPkg
  obtain ⟨requestUnary, locatedUnary, _rationalUnary, dyadicUnary, streamUnary,
    _readbackUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have cellUnary : UnaryHistory cellRead :=
    unary_cont_closed requestUnary locatedUnary requestLocated
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed cellUnary dyadicUnary cellDyadic
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed dyadicReadUnary streamUnary dyadicWindow
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary realSealUnary windowSeal
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro sealRead sourceSeal
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, requestLocated, cellDyadic, dyadicWindow, windowSeal, sealPkg⟩
    }
  · exact ⟨dyadicReadUnary, windowReadUnary, sealUnary⟩

theorem LocatednessModulusCarrier_public_export [AskSetup] [PackageSetup]
    {request locatedInterval rationalCells dyadicRows streamWindow readback realSeal transport
      replay provenance localName cellRead dyadicRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatednessModulusCarrier request locatedInterval rationalCells dyadicRows streamWindow
        readback realSeal transport replay provenance localName bundle pkg →
      Cont request locatedInterval cellRead →
        Cont cellRead dyadicRows dyadicRead →
          Cont dyadicRead streamWindow windowRead →
            Cont windowRead realSeal sealRead →
              PkgSig bundle provenance pkg →
                PkgSig bundle sealRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row request ∨ hsame row locatedInterval ∨
                          hsame row rationalCells ∨ hsame row dyadicRows ∨
                            hsame row streamWindow ∨ hsame row readback ∨
                              hsame row realSeal ∨ hsame row transport ∨
                                hsame row replay ∨ hsame row provenance ∨
                                  hsame row localName ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle sealRead pkg)
                      hsame ∧
                    UnaryHistory cellRead ∧ UnaryHistory dyadicRead ∧
                      UnaryHistory windowRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: LocatednessModulusCarrier BHist ProbeBundle Pkg Cont hsame
  -- SemanticNameCert UnaryHistory
  intro carrier requestLocated cellDyadic dyadicWindow windowSeal provenancePkg sealPkg
  obtain ⟨requestUnary, locatedUnary, _rationalUnary, dyadicUnary, streamUnary,
    _readbackUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _carrierProvenancePkg, _localNamePkg⟩ := carrier
  have cellUnary : UnaryHistory cellRead :=
    unary_cont_closed requestUnary locatedUnary requestLocated
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed cellUnary dyadicUnary cellDyadic
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed dyadicReadUnary streamUnary dyadicWindow
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary realSealUnary windowSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row request ∨ hsame row locatedInterval ∨ hsame row rationalCells ∨
              hsame row dyadicRows ∨ hsame row streamWindow ∨ hsame row readback ∨
                hsame row realSeal ∨ hsame row transport ∨ hsame row replay ∨
                  hsame row provenance ∨ hsame row localName ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, cellUnary, dyadicReadUnary, windowReadUnary, sealUnary⟩

theorem LocatednessModulusCarrier_real_seal_non_escape [AskSetup] [PackageSetup]
    {request locatedInterval rationalCells dyadicRows streamWindow readback realSeal transport
      replay provenance localName cellRead dyadicRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatednessModulusCarrier request locatedInterval rationalCells dyadicRows streamWindow
        readback realSeal transport replay provenance localName bundle pkg →
      Cont request locatedInterval cellRead →
        Cont cellRead dyadicRows dyadicRead →
          Cont dyadicRead streamWindow windowRead →
            Cont windowRead realSeal sealRead →
              PkgSig bundle provenance pkg →
                PkgSig bundle localName pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row request ∨ hsame row locatedInterval ∨
                          hsame row rationalCells ∨ hsame row dyadicRows ∨
                            hsame row streamWindow ∨ hsame row readback ∨
                              hsame row realSeal ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont request locatedInterval cellRead ∧
                          Cont cellRead dyadicRows dyadicRead ∧
                            Cont dyadicRead streamWindow windowRead ∧
                              Cont windowRead realSeal sealRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle localName pkg)
                      hsame ∧
                    UnaryHistory cellRead ∧ UnaryHistory dyadicRead ∧
                      UnaryHistory windowRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: LocatednessModulusCarrier BHist ProbeBundle Pkg Cont hsame
  -- SemanticNameCert UnaryHistory
  intro carrier requestLocated cellDyadic dyadicWindow windowSeal provenancePkg localNamePkg
  obtain ⟨requestUnary, locatedUnary, _rationalUnary, dyadicUnary, streamUnary,
    _readbackUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have cellUnary : UnaryHistory cellRead :=
    unary_cont_closed requestUnary locatedUnary requestLocated
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed cellUnary dyadicUnary cellDyadic
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed dyadicReadUnary streamUnary dyadicWindow
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary realSealUnary windowSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row request ∨ hsame row locatedInterval ∨ hsame row rationalCells ∨
              hsame row dyadicRows ∨ hsame row streamWindow ∨ hsame row readback ∨
                hsame row realSeal ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont request locatedInterval cellRead ∧
              Cont cellRead dyadicRows dyadicRead ∧ Cont dyadicRead streamWindow windowRead ∧
                Cont windowRead realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, requestLocated, cellDyadic, dyadicWindow, windowSeal,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, cellUnary, dyadicReadUnary, windowReadUnary, sealUnary⟩

theorem LocatednessModulusCarrier_window_transport [AskSetup] [PackageSetup]
    {request locatedInterval rationalCells dyadicRows streamWindow readback realSeal transport
      replay provenance localName cellRead dyadicRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatednessModulusCarrier request locatedInterval rationalCells dyadicRows streamWindow
        readback realSeal transport replay provenance localName bundle pkg →
      Cont request locatedInterval cellRead →
        Cont cellRead dyadicRows dyadicRead →
          Cont dyadicRead streamWindow windowRead →
            Cont windowRead realSeal sealRead →
              PkgSig bundle provenance pkg →
                PkgSig bundle sealRead pkg →
                  UnaryHistory request ∧ UnaryHistory locatedInterval ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory windowRead ∧
                      UnaryHistory sealRead ∧
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row request ∨ hsame row locatedInterval ∨
                                hsame row dyadicRows ∨ hsame row streamWindow ∨
                                  hsame row realSeal ∨ hsame row sealRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont request locatedInterval cellRead ∧
                                Cont cellRead dyadicRows dyadicRead ∧
                                  Cont dyadicRead streamWindow windowRead ∧
                                    Cont windowRead realSeal sealRead ∧
                                      PkgSig bundle sealRead pkg)
                            hsame := by
  -- BEDC touchpoint anchor: LocatednessModulusCarrier BHist ProbeBundle Pkg Cont hsame
  -- SemanticNameCert UnaryHistory
  intro carrier requestLocated cellDyadic dyadicWindow windowSeal _provenancePkg sealPkg
  obtain ⟨requestUnary, locatedUnary, _rationalUnary, dyadicUnary, streamUnary,
    _readbackUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _carrierProvenancePkg, _localNamePkg⟩ := carrier
  have cellUnary : UnaryHistory cellRead :=
    unary_cont_closed requestUnary locatedUnary requestLocated
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed cellUnary dyadicUnary cellDyadic
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed dyadicReadUnary streamUnary dyadicWindow
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary realSealUnary windowSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row request ∨ hsame row locatedInterval ∨ hsame row dyadicRows ∨
              hsame row streamWindow ∨ hsame row realSeal ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont request locatedInterval cellRead ∧
              Cont cellRead dyadicRows dyadicRead ∧ Cont dyadicRead streamWindow windowRead ∧
                Cont windowRead realSeal sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, requestLocated, cellDyadic, dyadicWindow, windowSeal, sealPkg⟩
  }
  exact ⟨requestUnary, locatedUnary, dyadicReadUnary, windowReadUnary, sealUnary, cert⟩

end BEDC.Derived.LocatednessModulusUp
