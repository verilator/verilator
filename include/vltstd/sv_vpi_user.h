/***************************************************************************
* sv_vpi_user.h
*
* SystemVerilog VPI extensions.
*
* This file contains the constant definitions, structure definitions, and
* routine declarations used by the SystemVerilog Verification Procedural
* Interface (VPI) access routines.
*
**************************************************************************/

/***************************************************************************
* NOTE:
* The constant values 600 through 999 are reserved for use in this file.
* - the range 600-749 is reserved for SV VPI model extensions
* - the range 750-779 is reserved for the Coverage VPI
* - the range 800-899 is reserved for future use
* Overlaps in the numerical ranges are permitted for different categories
* of identifiers; e.g.
* - object types
* - properties
* - callbacks
**************************************************************************/

#ifndef SV_VPI_USER_H
#define SV_VPI_USER_H

#include "vpi_user.h"

#ifdef __cplusplus
extern "C" {
#endif

/****************************** OBJECT TYPES ******************************/
#define vpiPackage                  600
#define vpiInterface                601
#define vpiProgram                  602
#define vpiInterfaceArray           603
#define vpiProgramArray             604
#define vpiTypespec                 605
#define vpiModport                  606
#define vpiInterfaceTfDecl          607
#define vpiRefObj                   608
#define vpiTypeParameter            609

/* variables */
#define vpiVarBit                   vpiRegBit
#define vpiLongIntVar               610
#define vpiShortIntVar              611
#define vpiIntVar                   612
#define vpiShortRealVar             613
#define vpiByteVar                  614
#define vpiClassVar                 615
#define vpiStringVar                616
#define vpiEnumVar                  617
#define vpiStructVar                618
#define vpiUnionVar                 619
#define vpiBitVar                   620
#define vpiLogicVar                 vpiReg
#define vpiArrayVar                 vpiRegArray
#define vpiClassObj                 621
#define vpiChandleVar               622
#define vpiPackedArrayVar           623
#define vpiVirtualInterfaceVar      728

/* typespecs */
#define vpiLongIntTypespec          625
#define vpiShortRealTypespec        626
#define vpiByteTypespec             627
#define vpiShortIntTypespec         628
#define vpiIntTypespec              629
#define vpiClassTypespec            630
#define vpiStringTypespec           631
#define vpiChandleTypespec          632
#define vpiEnumTypespec             633
#define vpiEnumConst                634
#define vpiIntegerTypespec          635
#define vpiTimeTypespec             636
#define vpiRealTypespec             637
#define vpiStructTypespec           638
#define vpiUnionTypespec            639
#define vpiBitTypespec              640
#define vpiLogicTypespec            641
#define vpiArrayTypespec            642
#define vpiVoidTypespec             643
#define vpiTypespecMember           644
#define vpiPackedArrayTypespec      692
#define vpiSequenceTypespec         696
#define vpiPropertyTypespec         697
#define vpiEventTypespec            698
#define vpiInterfaceTypespec        906

#define vpiClockingBlock            650
#define vpiClockingIODecl           651
#define vpiClassDefn                652
#define vpiConstraint               653
#define vpiConstraintOrdering       654

#define vpiDistItem                 645
#define vpiAliasStmt                646
#define vpiThread                   647
#define vpiMethodFuncCall           648
#define vpiMethodTaskCall           649

/* concurrent assertions */
#define vpiAssert                   686
#define vpiAssume                   687
#define vpiCover                    688
#define vpiRestrict                 901

#define vpiDisableCondition         689
#define vpiClockingEvent            690
/* property decl, spec */
#define vpiPropertyDecl             655
#define vpiPropertySpec             656
#define vpiPropertyExpr             657
#define vpiMulticlockSequenceExpr   658
#define vpiClockedSeq               659
#define vpiClockedProp              902
#define vpiPropertyInst             660
#define vpiSequenceDecl             661
#define vpiCaseProperty             662 /* property case */
#define vpiCasePropertyItem         905 /* property case item */
#define vpiSequenceInst             664
#define vpiImmediateAssert          665
#define vpiImmediateAssume          694
#define vpiImmediateCover           695
#define vpiReturn                   666
/* pattern */
#define vpiAnyPattern               667
#define vpiTaggedPattern            668
#define vpiStructPattern            669
/* do .. while */
#define vpiDoWhile                  670
/* waits */
#define vpiOrderedWait              671
#define vpiWaitFork                 672
/* disables */
#define vpiDisableFork              673
#define vpiExpectStmt               674
#define vpiForeachStmt              675
#define vpiReturnStmt               691
#define vpiFinal                    676
#define vpiExtends                  677
#define vpiDistribution             678
#define vpiSeqFormalDecl            679
#define vpiPropFormalDecl           699
#define vpiArrayNet                 vpiNetArray
#define vpiEnumNet                  680
#define vpiIntegerNet               681
#define vpiLogicNet                 vpiNet
#define vpiTimeNet                  682
#define vpiUnionNet                 525
#define vpiShortRealNet             526
#define vpiRealNet                  527
#define vpiByteNet                  528
#define vpiShortIntNet              529
#define vpiIntNet                   530
#define vpiLongIntNet               531
#define vpiBitNet                   532
#define vpiInterconnectNet          533
#define vpiInterconnectArray        534
#define vpiStructNet                683
#define vpiBreak                    684
#define vpiContinue                 685
#define vpiPackedArrayNet           693
#define vpiNettypeDecl              523
#define vpiConstraintExpr           747
#define vpiElseConst                748
#define vpiImplication              749
#define vpiConstrIf                 738
#define vpiConstrIfElse             739
#define vpiConstrForEach            736
#define vpiSoftDisable              733
#define vpiLetDecl                  903
#define vpiLetExpr                  904

/******************************** METHODS *********************************/
/************* methods used to traverse 1 to 1 relationships **************/
#define vpiActual                   700

#define vpiTypedefAlias             701

#define vpiIndexTypespec            702
#define vpiBaseTypespec             703
#define vpiElemTypespec             704

#define vpiNetTypedefAlias          705

#define vpiInputSkew                706
#define vpiOutputSkew               707
#define vpiGlobalClocking           708
#define vpiDefaultClocking          709
#define vpiDefaultDisableIff        710

#define vpiOrigin                   713
#define vpiPrefix                   714
#define vpiWith                     715

#define vpiProperty                 718

#define vpiValueRange               720
#define vpiPattern                  721
#define vpiWeight                   722
#define vpiConstraintItem           746

/************ methods used to traverse 1 to many relationships ************/
#define vpiTypedef                  725
#define vpiImport                   726
#define vpiDerivedClasses           727
#define vpiInterfaceDecl    vpiVirtualInterfaceVar /* interface decl deprecated */

#define vpiMethods                  730
#define vpiSolveBefore              731
#define vpiSolveAfter               732

#define vpiWaitingProcesses         734

#define vpiMessages                 735
#define vpiLoopVars                 737

#define vpiConcurrentAssertion      740
#define vpiConcurrentAssertions     vpiConcurrentAssertion
#define vpiMatchItem                741
#define vpiMember                   742
#define vpiElement                  743

/************* methods used to traverse 1 to many relationships ***************/
#define vpiAssertion                744

/*********** methods used to traverse both 1-1 and 1-many relations ***********/
#define vpiInstance                 745


/**************************************************************************/
/************************ generic object properties ***********************/
/**************************************************************************/

#define vpiTop                      600

#define vpiUnit                     602

#define vpiJoinType                 603
#define vpiJoin                 0
#define vpiJoinNone             1
#define vpiJoinAny              2

#define vpiAccessType               604
#define vpiForkJoinAcc          1
#define vpiExternAcc            2
#define vpiDPIExportAcc         3
#define vpiDPIImportAcc         4

#define vpiArrayType                606
#define vpiStaticArray          1
#define vpiDynamicArray         2
#define vpiAssocArray           3
#define vpiQueueArray           4
#define vpiArrayMember              607

#define vpiIsRandomized             608
#define vpiLocalVarDecls            609
#define vpiOpStrong                 656 /* strength of temporal operator */
#define vpiRandType                 610
#define vpiNotRand              1
#define vpiRand                 2
#define vpiRandC                3
#define vpiPortType                 611
#define vpiInterfacePort        1
#define vpiModportPort          2
/* vpiPort is also a port type. It is defined in vpi_user.h */

#define vpiConstantVariable         612
#define vpiStructUnionMember        615

#define vpiVisibility               620
#define vpiPublicVis            1
#define vpiProtectedVis         2
#define vpiLocalVis             3

/* Return values for vpiConstType property */
#define vpiOneStepConst         9
#define vpiUnboundedConst       10
#define vpiNullConst            11

#define vpiAlwaysType               624
#define vpiAlwaysComb           2
#define vpiAlwaysFF             3
#define vpiAlwaysLatch          4

#define vpiDistType                 625
#define vpiEqualDist            1 /* constraint equal distribution */
#define vpiDivDist              2 /* constraint divided distribution */

#define vpiPacked                   630
#define vpiTagged                   632
#define vpiRef                  6 /* Return value for vpiDirection property */
#define vpiVirtual                  635
#define vpiHasActual                636
#define vpiIsConstraintEnabled      638
#define vpiSoft                     639


#define vpiClassType                640
#define vpiMailboxClass         1
#define vpiSemaphoreClass       2
#define vpiUserDefinedClass     3
#define vpiProcessClass         4

#define vpiMethod                   645
#define vpiIsClockInferred          649
#define vpiIsDeferred               657
#define vpiIsFinal                  670
#define vpiIsCoverSequence          659
#define vpiQualifier                650
#define vpiNoQualifier          0
#define vpiUniqueQualifier      1
#define vpiPriorityQualifier    2
#define vpiTaggedQualifier      4
#define vpiRandQualifier        8
#define vpiInsideQualifier      16

#define vpiInputEdge                651 /* returns vpiNoEdge, vpiPosedge,
                                           vpiNegedge */
#define vpiOutputEdge               652 /* returns vpiNoEdge, vpiPosedge,
                                           vpiNegedge */
#define vpiGeneric                  653

/* Compatibility-mode property and values (object argument == NULL) */
#define vpiCompatibilityMode        654
#define vpiMode1364v1995        1
#define vpiMode1364v2001        2
#define vpiMode1364v2005        3
#define vpiMode1800v2005        4
#define vpiMode1800v2009        5

#define vpiPackedArrayMember        655
#define vpiStartLine                661
#define vpiColumn                   662
#define vpiEndLine                  663
#define vpiEndColumn                664

/* memory allocation scheme for transient objects */
#define vpiAllocScheme              658
#define vpiAutomaticScheme      1
#define vpiDynamicScheme        2
#define vpiOtherScheme          3

#define vpiObjId                    660

#define vpiDPIPure                  665
#define vpiDPIContext               666
#define vpiDPICStr                  667
#define vpiDPI                  1
#define vpiDPIC                 2
#define vpiDPICIdentifier           668
#define vpiIsModPort                669

/******************************** Operators *******************************/
#define vpiImplyOp                  50 /* -> implication operator */
#define vpiNonOverlapImplyOp        51 /* |=> nonoverlapped implication */
#define vpiOverlapImplyOp           52 /* |-> overlapped implication operator */
#define vpiAcceptOnOp               83 /* accept_on operator */
#define vpiRejectOnOp               84 /* reject_on operator */
#define vpiSyncAcceptOnOp           85 /* sync_accept_on operator */
#define vpiSyncRejectOnOp           86 /* sync_reject_on operator */
#define vpiOverlapFollowedByOp      87 /* overlapped followed_by operator */
#define vpiNonOverlapFollowedByOp   88 /* nonoverlapped followed_by operator */
#define vpiNexttimeOp               89 /* nexttime operator */
#define vpiAlwaysOp                 90 /* always operator */
#define vpiEventuallyOp             91 /* eventually operator */
#define vpiUntilOp                  92 /* until operator */
#define vpiUntilWithOp              93 /* until_with operator */

#define vpiUnaryCycleDelayOp        53 /* binary cycle delay (##) operator */
#define vpiCycleDelayOp             54 /* binary cycle delay (##) operator */
#define vpiIntersectOp              55 /* intersection operator */
#define vpiFirstMatchOp             56 /* first_match operator */
#define vpiThroughoutOp             57 /* throughout operator */
#define vpiWithinOp                 58 /* within operator */
#define vpiRepeatOp                 59 /* [=] nonconsecutive repetition */
#define vpiConsecutiveRepeatOp      60 /* [*] consecutive repetition */
#define vpiGotoRepeatOp             61 /* [->] goto repetition */

#define vpiPostIncOp                62 /* ++ post-increment */
#define vpiPreIncOp                 63 /* ++ pre-increment */
#define vpiPostDecOp                64 /* -- post-decrement */
#define vpiPreDecOp                 65 /* -- pre-decrement */

#define vpiMatchOp                  66 /* match() operator */
#define vpiCastOp                   67 /* type'() operator */
#define vpiIffOp                    68 /* iff operator */
#define vpiWildEqOp                 69 /* ==? operator */
#define vpiWildNeqOp                70 /* !=? operator */

#define vpiStreamLROp               71 /* left-to-right streaming {>>} operator */
#define vpiStreamRLOp               72 /* right-to-left streaming {<<} operator */

#define vpiMatchedOp                73 /* the .matched sequence operation */
#define vpiTriggeredOp              74 /* the .triggered sequence operation */
#define vpiAssignmentPatternOp      75 /* '{} assignment pattern */
#define vpiMultiAssignmentPatternOp 76 /* '{n{}} multi assignment pattern */
#define vpiIfOp                     77 /* if operator */
#define vpiIfElseOp                 78 /* if-else operator */
#define vpiCompAndOp                79 /* Composite and operator */
#define vpiCompOrOp                 80 /* Composite or operator */
#define vpiImpliesOp                94 /* implies operator */
#define vpiInsideOp                 95 /* inside operator */
#define vpiTypeOp                   81 /* type operator */
#define vpiAssignmentOp             82 /* Normal assignment */

/*********************** task/function properties ***********************/
#define vpiOtherFunc                6 /* returns other types; for property vpiFuncType */

/* vpiValid and vpiValidUnknown were deprecated in 1800-2009 */
/*********************** value for vpiValid *****************************/
#define vpiValidUnknown             2 /* Validity of variable is unknown */

/************************** STRUCTURE DEFINITIONS *************************/

/***************************** structure *****************************/

/**************************** CALLBACK REASONS ****************************/
#define vpiMethodFuncCall           648
#define cbStartOfThread             600 /* callback on thread creation */
#define cbEndOfThread               601 /* callback on thread termination */
#define cbEnterThread               602 /* callback on reentering thread */
#define cbStartOfFrame              603 /* callback on frame creation */
#define cbEndOfFrame                604 /* callback on frame exit */
#define cbSizeChange                605 /* callback on array variable size change */
#define cbCreateObj                 700 /* callback on class object creation */
#define cbReclaimObj                701 /* callback on class object reclaimed by
                                           automatic memory management */
#define cbEndOfObject               702 /* callback on transient object deletion */

/************************* FUNCTION DECLARATIONS **************************/


/**************************************************************************/
/*************************** Coverage VPI *********************************/
/**************************************************************************/

/* coverage control */
#define vpiCoverageStart            750
#define vpiCoverageStop             751
#define vpiCoverageReset            752
#define vpiCoverageCheck            753
#define vpiCoverageMerge            754
#define vpiCoverageSave             755

/* coverage type properties */
#define vpiAssertCoverage           760
#define vpiFsmStateCoverage         761
#define vpiStatementCoverage        762
#define vpiToggleCoverage           763

/* coverage status properties */
#define vpiCovered                  765
#define vpiCoverMax                 766 /* preserved for backward compatibility */
#define vpiCoveredMax               766
#define vpiCoveredCount             767

/* assertion-specific coverage status properties */
#define vpiAssertAttemptCovered     770
#define vpiAssertSuccessCovered     771
#define vpiAssertFailureCovered     772
#define vpiAssertVacuousSuccessCovered 773
#define vpiAssertDisableCovered     774
#define vpiAssertKillCovered        777

/* FSM-specific coverage status properties */
#define vpiFsmStates                775
#define vpiFsmStateExpression       776

/* FSM handle types */
#define vpiFsm                      758
#define vpiFsmHandle                759


/***************************************************************************/
/***************************** Assertion VPI *******************************/
/***************************************************************************/

/* assertion callback types */
#define cbAssertionStart                        606
#define cbAssertionSuccess                      607
#define cbAssertionFailure                      608
#define cbAssertionVacuousSuccess               657
#define cbAssertionDisabledEvaluation           658
#define cbAssertionStepSuccess                  609
#define cbAssertionStepFailure                  610
#define cbAssertionLock                         661
#define cbAssertionUnlock                       662
#define cbAssertionDisable                      611
#define cbAssertionEnable                       612
#define cbAssertionReset                        613
#define cbAssertionKill                         614
#define cbAssertionEnablePassAction             645
#define cbAssertionEnableFailAction             646
#define cbAssertionDisablePassAction            647
#define cbAssertionDisableFailAction            648
#define cbAssertionEnableNonvacuousAction       649
#define cbAssertionDisableVacuousAction         650

/* assertion "system" callback types */
#define cbAssertionSysInitialized               615
#define cbAssertionSysOn                        616
#define cbAssertionSysOff                       617
#define cbAssertionSysKill                      631
#define cbAssertionSysLock                      659
#define cbAssertionSysUnlock                    660
#define cbAssertionSysEnd                       618
#define cbAssertionSysReset                     619
#define cbAssertionSysEnablePassAction          651
#define cbAssertionSysEnableFailAction          652
#define cbAssertionSysDisablePassAction         653
#define cbAssertionSysDisableFailAction         654
#define cbAssertionSysEnableNonvacuousAction    655
#define cbAssertionSysDisableVacuousAction      656

/* assertion control constants */
#define vpiAssertionLock                        645
#define vpiAssertionUnlock                      646
#define vpiAssertionDisable                     620
#define vpiAssertionEnable                      621
#define vpiAssertionReset                       622
#define vpiAssertionKill                        623
#define vpiAssertionEnableStep                  624
#define vpiAssertionDisableStep                 625
#define vpiAssertionClockSteps                  626
#define vpiAssertionSysLock                     647
#define vpiAssertionSysUnlock                   648
#define vpiAssertionSysOn                       627
#define vpiAssertionSysOff                      628
#define vpiAssertionSysKill                     632
#define vpiAssertionSysEnd                      629
#define vpiAssertionSysReset                    630
#define vpiAssertionDisablePassAction           633
#define vpiAssertionEnablePassAction            634
#define vpiAssertionDisableFailAction           635
#define vpiAssertionEnableFailAction            636
#define vpiAssertionDisableVacuousAction        637
#define vpiAssertionEnableNonvacuousAction      638
#define vpiAssertionSysEnablePassAction         639
#define vpiAssertionSysEnableFailAction         640
#define vpiAssertionSysDisablePassAction        641
#define vpiAssertionSysDisableFailAction        642
#define vpiAssertionSysEnableNonvacuousAction   643
#define vpiAssertionSysDisableVacuousAction     644

typedef struct t_vpi_assertion_step_info {
    PLI_INT32 matched_expression_count;
    vpiHandle *matched_exprs;       /* array of expressions */
    PLI_INT32 stateFrom, stateTo;   /* identify transition */
} s_vpi_assertion_step_info, *p_vpi_assertion_step_info;

typedef struct t_vpi_attempt_info {
    union {
        vpiHandle failExpr;
        p_vpi_assertion_step_info step;
    } detail;
    s_vpi_time attemptStartTime;    /* Time attempt triggered */
} s_vpi_attempt_info, *p_vpi_attempt_info;

/* typedef for vpi_register_assertion_cb callback function */
typedef PLI_INT32(vpi_assertion_callback_func)(
    PLI_INT32 reason,               /* callback reason */
    p_vpi_time cb_time,             /* callback time */
    vpiHandle assertion,            /* handle to assertion */
    p_vpi_attempt_info info,        /* attempt related information */
    PLI_BYTE8 *user_data            /* user data entered upon registration */
);

vpiHandle vpi_register_assertion_cb(
    vpiHandle assertion,            /* handle to assertion */
    PLI_INT32 reason,               /* reason for which callbacks needed */
    vpi_assertion_callback_func *cb_rtn,
    PLI_BYTE8 *user_data            /* user data to be supplied to cb */
);

#ifdef __cplusplus
}
#endif

#endif
