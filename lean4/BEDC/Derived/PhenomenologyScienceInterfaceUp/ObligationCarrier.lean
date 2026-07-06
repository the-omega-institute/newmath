import BEDC.Derived.PhenomenologyScienceInterfaceUp.InvariantTransport
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PhenomenologyScienceInterfaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PhenomenologyScienceInterface_obligation_carrier [AskSetup] [PackageSetup]
    {R U O L S J B G H C P N observationRead scienceRead bridgeRead preservedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N R →
      PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N U →
        PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N O →
          PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N L →
            PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N S →
              PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N J →
                PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N B →
                  PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N G →
                    UnaryHistory R →
                      UnaryHistory U →
                        UnaryHistory O →
                          UnaryHistory L →
                            UnaryHistory S →
                              UnaryHistory J →
                                UnaryHistory B →
                                  UnaryHistory G →
                                    UnaryHistory H →
                                      UnaryHistory C →
                                        UnaryHistory P →
                                          UnaryHistory N →
                                            Cont R U observationRead →
                                              Cont S J scienceRead →
                                                Cont scienceRead B bridgeRead →
                                                  Cont observationRead bridgeRead
                                                    preservedRead →
                                                    PkgSig bundle preservedRead pkg →
                                                      SemanticNameCert
                                                          (fun row : BHist =>
                                                            hsame row preservedRead ∧
                                                              UnaryHistory row)
                                                          (fun row : BHist =>
                                                            PhenomenologyScienceInterfaceObligationRowSpec
                                                                R U O L S J B G H C P N row ∨
                                                              hsame row observationRead ∨
                                                                hsame row scienceRead ∨
                                                                  hsame row bridgeRead ∨
                                                                    hsame row preservedRead)
                                                          (fun row : BHist =>
                                                            UnaryHistory row ∧
                                                              Cont R U observationRead ∧
                                                                Cont S J scienceRead ∧
                                                                  Cont scienceRead B bridgeRead ∧
                                                                    Cont observationRead
                                                                      bridgeRead preservedRead ∧
                                                                      PkgSig bundle
                                                                        preservedRead pkg)
                                                          hsame ∧
                                                        UnaryHistory observationRead ∧
                                                          UnaryHistory scienceRead ∧
                                                            UnaryHistory bridgeRead ∧
                                                              UnaryHistory preservedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _rSpec _uSpec _oSpec _lSpec _sSpec _jSpec _bSpec _gSpec rUnary uUnary _oUnary
    _lUnary sUnary jUnary bUnary _gUnary _hUnary _cUnary _pUnary _nUnary observationRoute
    scienceRoute bridgeRoute preservedRoute packageEvidence
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed rUnary uUnary observationRoute
  have scienceUnary : UnaryHistory scienceRead :=
    unary_cont_closed sUnary jUnary scienceRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed scienceUnary bUnary bridgeRoute
  have preservedUnary : UnaryHistory preservedRead :=
    unary_cont_closed observationUnary bridgeUnary preservedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row preservedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N row ∨
              hsame row observationRead ∨ hsame row scienceRead ∨ hsame row bridgeRead ∨
                hsame row preservedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R U observationRead ∧ Cont S J scienceRead ∧
              Cont scienceRead B bridgeRead ∧ Cont observationRead bridgeRead preservedRead ∧
                PkgSig bundle preservedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro preservedRead ⟨hsame_refl preservedRead, preservedUnary⟩
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
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, observationRoute, scienceRoute, bridgeRoute, preservedRoute,
          packageEvidence⟩
  }
  exact ⟨cert, observationUnary, scienceUnary, bridgeUnary, preservedUnary⟩

theorem PhenomenologyScienceInterfaceTasteGate_obligation_scope [AskSetup] [PackageSetup]
    {R U O L S J B G H C P N observationRead scienceRead bridgeRead preservedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N R →
      PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N U →
        PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N O →
          PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N L →
            PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N S →
              PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N J →
                PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N B →
                  PhenomenologyScienceInterfaceObligationRowSpec R U O L S J B G H C P N G →
                    UnaryHistory R →
                      UnaryHistory U →
                        UnaryHistory O →
                          UnaryHistory L →
                            UnaryHistory S →
                              UnaryHistory J →
                                UnaryHistory B →
                                  UnaryHistory G →
                                    UnaryHistory H →
                                      UnaryHistory C →
                                        UnaryHistory P →
                                          UnaryHistory N →
                                            Cont R U observationRead →
                                              Cont S J scienceRead →
                                                Cont scienceRead B bridgeRead →
                                                  Cont observationRead bridgeRead
                                                    preservedRead →
                                                    PkgSig bundle preservedRead pkg →
                                                      SemanticNameCert
                                                          (fun row : BHist =>
                                                            hsame row preservedRead ∧
                                                              UnaryHistory row)
                                                          (fun row : BHist =>
                                                            PhenomenologyScienceInterfaceObligationRowSpec
                                                                R U O L S J B G H C P N row ∨
                                                              hsame row observationRead ∨
                                                                hsame row scienceRead ∨
                                                                  hsame row bridgeRead ∨
                                                                    hsame row preservedRead)
                                                          (fun row : BHist =>
                                                            UnaryHistory row ∧
                                                              Cont R U observationRead ∧
                                                                Cont S J scienceRead ∧
                                                                  Cont scienceRead B bridgeRead ∧
                                                                    Cont observationRead
                                                                      bridgeRead preservedRead ∧
                                                                      PkgSig bundle
                                                                        preservedRead pkg)
                                                          hsame ∧
                                                        PhenomenologyScienceInterfaceObligationRowSpec
                                                          R U O L S J B G H C P N R ∧
                                                          PhenomenologyScienceInterfaceObligationRowSpec
                                                            R U O L S J B G H C P N U ∧
                                                            PhenomenologyScienceInterfaceObligationRowSpec
                                                              R U O L S J B G H C P N O ∧
                                                              PhenomenologyScienceInterfaceObligationRowSpec
                                                                R U O L S J B G H C P N L ∧
                                                                PhenomenologyScienceInterfaceObligationRowSpec
                                                                  R U O L S J B G H C P N S ∧
                                                                  PhenomenologyScienceInterfaceObligationRowSpec
                                                                    R U O L S J B G H C P N J ∧
                                                                    PhenomenologyScienceInterfaceObligationRowSpec
                                                                      R U O L S J B G H C P N B ∧
                                                                      PhenomenologyScienceInterfaceObligationRowSpec
                                                                        R U O L S J B G H C P N G := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert
  intro rSpec uSpec oSpec lSpec sSpec jSpec bSpec gSpec rUnary uUnary oUnary lUnary
    sUnary jUnary bUnary gUnary hUnary cUnary pUnary nUnary observationRoute scienceRoute
    bridgeRoute preservedRoute packageEvidence
  have certPacket :=
    PhenomenologyScienceInterface_obligation_carrier
      (R := R) (U := U) (O := O) (L := L) (S := S) (J := J) (B := B) (G := G)
      (H := H) (C := C) (P := P) (N := N) (observationRead := observationRead)
      (scienceRead := scienceRead) (bridgeRead := bridgeRead) (preservedRead := preservedRead)
      (bundle := bundle) (pkg := pkg) rSpec uSpec oSpec lSpec sSpec jSpec bSpec gSpec
      rUnary uUnary oUnary lUnary sUnary jUnary bUnary gUnary hUnary cUnary pUnary nUnary
      observationRoute scienceRoute bridgeRoute preservedRoute packageEvidence
  exact
    ⟨certPacket.left, rSpec, uSpec, oSpec, lSpec, sSpec, jSpec, bSpec, gSpec⟩

end BEDC.Derived.PhenomenologyScienceInterfaceUp
