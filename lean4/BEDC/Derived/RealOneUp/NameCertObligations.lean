import BEDC.Derived.RealOneUp.RationalEmbeddingRoute
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealOneUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealOneNameCertObligations [AskSetup] [PackageSetup]
    {seed constantWindow regularReadback dyadicUnit realSeal _transport _replay provenance localName
      stationaryRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory seed →
      UnaryHistory constantWindow →
        UnaryHistory regularReadback →
          UnaryHistory dyadicUnit →
            UnaryHistory realSeal →
              UnaryHistory provenance →
                Cont seed constantWindow stationaryRead →
                  Cont stationaryRead regularReadback dyadicUnit →
                    Cont dyadicUnit realSeal terminalRead →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle localName pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row seed ∨ hsame row constantWindow ∨
                                  hsame row regularReadback ∨ hsame row dyadicUnit ∨
                                    hsame row realSeal ∨ hsame row terminalRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle localName pkg)
                              hsame ∧
                            UnaryHistory stationaryRead ∧ UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro seedUnary windowUnary readbackUnary dyadicUnitUnary realSealUnary _provenanceUnary
    stationaryRoute dyadicRoute terminalRoute provenancePkg localNamePkg
  have stationaryUnary : UnaryHistory stationaryRead :=
    unary_cont_closed seedUnary windowUnary stationaryRoute
  have _dyadicUnitUnaryFromRoute : UnaryHistory dyadicUnit :=
    unary_cont_closed stationaryUnary readbackUnary dyadicRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed dyadicUnitUnary realSealUnary terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row seed ∨ hsame row constantWindow ∨ hsame row regularReadback ∨
              hsame row dyadicUnit ∨ hsame row realSeal ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro terminalRead ⟨hsame_refl terminalRead, terminalUnary⟩
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
        exact ⟨source.right, provenancePkg, localNamePkg⟩
    }
  exact ⟨cert, stationaryUnary, terminalUnary⟩

end BEDC.Derived.RealOneUp
