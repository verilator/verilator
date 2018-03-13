/*******************************************************************************
 * vpi_user.h
 *
 * IEEE Std 1800-2017 Programming Language Interface (PLI)
 *
 * This file contains the constant definitions, structure definitions, and
 * routine declarations used by the SystemVerilog Verification Procedural
 * Interface (VPI) access routines.
 *
 ******************************************************************************/

/*******************************************************************************
 * NOTE: the constant values 1 through 299 are reserved for use in this
 * vpi_user.h file.
 ******************************************************************************/

#ifndef VPI_USER_H
#define VPI_USER_H

#include <stdarg.h>

#ifdef __cplusplus
extern "C" {
#endif

/*----------------------------------------------------------------------------*/
/*----------------------------- Portability Help -----------------------------*/
/*----------------------------------------------------------------------------*/

/* Define size-critical types on all OS platforms. */
#if defined (_MSC_VER)
typedef unsigned __int64 uint64_t;
typedef unsigned __int32 uint32_t;
typedef unsigned __int8 uint8_t;
typedef signed __int64 int64_t;
typedef signed __int32 int32_t;
typedef signed __int8 int8_t;
#elif defined(__MINGW32__)
#include <stdint.h>
#elif defined(__linux) || (defined(__APPLE__) && defined(__MACH__))
#include <inttypes.h>
#else
#include <sys/types.h>
#endif

/* Sized variables */

#ifndef SVPI_TYPES
#define SVPI_TYPES
typedef int64_t PLI_INT64;
typedef uint64_t PLI_UINT64;
#endif

#ifndef PLI_TYPES
#define PLI_TYPES
typedef int              PLI_INT32;
typedef unsigned int     PLI_UINT32;
typedef short            PLI_INT16;
typedef unsigned short   PLI_UINT16;
typedef char             PLI_BYTE8;
typedef unsigned char    PLI_UBYTE8;
#endif

/* Use to import a symbol */

#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#ifndef PLI_DLLISPEC
#define PLI_DLLISPEC __declspec(dllimport)
#define VPI_USER_DEFINED_DLLISPEC 1
#endif
#else
#ifndef PLI_DLLISPEC
#define PLI_DLLISPEC
#endif
#endif

/* Use to export a symbol */

#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#ifndef PLI_DLLESPEC
#define PLI_DLLESPEC __declspec(dllexport)
#define VPI_USER_DEFINED_DLLESPEC 1
#endif
#else
#ifndef PLI_DLLESPEC
#define PLI_DLLESPEC
#endif
#endif

/* Use to mark a function as external */

#ifndef PLI_EXTERN
#define PLI_EXTERN
#endif

/* Use to mark a variable as external */

#ifndef PLI_VEXTERN
#define PLI_VEXTERN extern
#endif

#ifndef PLI_PROTOTYPES
#define PLI_PROTOTYPES
#define PROTO_PARAMS(params) params

/* object is defined imported by the application */

#undef XXTERN
#define XXTERN PLI_EXTERN PLI_DLLISPEC

/* object is exported by the application */

#undef EETERN
#define EETERN PLI_EXTERN PLI_DLLESPEC
#endif

/********************************** TYPEDEFS **********************************/

typedef PLI_UINT32 *vpiHandle;

/******************************** OBJECT TYPES ********************************/

#define vpiAlways              1   /* always procedure */
#define vpiAssignStmt          2   /* quasi-continuous assignment */
#define vpiAssignment          3   /* procedural assignment */
#define vpiBegin               4   /* block statement */
#define vpiCase                5   /* case statement */
#define vpiCaseItem            6   /* case statement item */
#define vpiConstant            7   /* numerical constant or string literal */
#define vpiContAssign          8   /* continuous assignment */
#define vpiDeassign            9   /* deassignment statement */
#define vpiDefParam           10   /* defparam */
#define vpiDelayControl       11   /* delay statement (e.g., #10) */
#define vpiDisable            12   /* named block disable statement */
#define vpiEventControl       13   /* wait on event, e.g., @e */
#define vpiEventStmt          14   /* event trigger, e.g., ->e */
#define vpiFor                15   /* for statement */
#define vpiForce              16   /* force statement */
#define vpiForever            17   /* forever statement */
#define vpiFork               18   /* fork-join block */
#define vpiFuncCall           19   /* function call */
#define vpiFunction           20   /* function */
#define vpiGate               21   /* primitive gate */
#define vpiIf                 22   /* if statement */
#define vpiIfElse             23   /* if-else statement */
#define vpiInitial            24   /* initial procedure */
#define vpiIntegerVar         25   /* integer variable */
#define vpiInterModPath       26   /* intermodule wire delay */
#define vpiIterator           27   /* iterator */
#define vpiIODecl             28   /* input/output declaration */
#define vpiMemory             29   /* behavioral memory */
#define vpiMemoryWord         30   /* single word of memory */
#define vpiModPath            31   /* module path for path delays */
#define vpiModule             32   /* module instance */
#define vpiNamedBegin         33   /* named block statement */
#define vpiNamedEvent         34   /* event variable */
#define vpiNamedFork          35   /* named fork-join block */
#define vpiNet                36   /* scalar or vector net */
#define vpiNetBit             37   /* bit of vector net */
#define vpiNullStmt           38   /* a semicolon. Ie. #10 ; */
#define vpiOperation          39   /* behavioral operation */
#define vpiParamAssign        40   /* module parameter assignment */
#define vpiParameter          41   /* module parameter */
#define vpiPartSelect         42   /* part-select */
#define vpiPathTerm           43   /* terminal of module path */
#define vpiPort               44   /* module port */
#define vpiPortBit            45   /* bit of vector module port */
#define vpiPrimTerm           46   /* primitive terminal */
#define vpiRealVar            47   /* real variable */
#define vpiReg                48   /* scalar or vector reg */
#define vpiRegBit             49   /* bit of vector reg */
#define vpiRelease            50   /* release statement */
#define vpiRepeat             51   /* repeat statement */
#define vpiRepeatControl      52   /* repeat control in an assign stmt */
#define vpiSchedEvent         53   /* vpi_put_value() event */
#define vpiSpecParam          54   /* specparam */
#define vpiSwitch             55   /* transistor switch */
#define vpiSysFuncCall        56   /* system function call */
#define vpiSysTaskCall        57   /* system task call */
#define vpiTableEntry         58   /* UDP state table entry */
#define vpiTask               59   /* task */
#define vpiTaskCall           60   /* task call */
#define vpiTchk               61   /* timing check */
#define vpiTchkTerm           62   /* terminal of timing check */
#define vpiTimeVar            63   /* time variable */
#define vpiTimeQueue          64   /* simulation event queue */
#define vpiUdp                65   /* user-defined primitive */
#define vpiUdpDefn            66   /* UDP definition */
#define vpiUserSystf          67   /* user-defined system task/function */
#define vpiVarSelect          68   /* variable array selection */
#define vpiWait               69   /* wait statement */
#define vpiWhile              70   /* while statement */

/********************** object types added with 1364-2001 *********************/

#define vpiAttribute         105   /* attribute of an object */
#define vpiBitSelect         106   /* Bit-select of parameter, var select */
#define vpiCallback          107   /* callback object */
#define vpiDelayTerm         108   /* Delay term which is a load or driver */
#define vpiDelayDevice       109   /* Delay object within a net */
#define vpiFrame             110   /* reentrant task/func frame */
#define vpiGateArray         111   /* gate instance array */
#define vpiModuleArray       112   /* module instance array */
#define vpiPrimitiveArray    113   /* vpiprimitiveArray type */
#define vpiNetArray          114   /* multidimensional net */
#define vpiRange             115   /* range declaration */
#define vpiRegArray          116   /* multidimensional reg */
#define vpiSwitchArray       117   /* switch instance array */
#define vpiUdpArray          118   /* UDP instance array */
#define vpiContAssignBit     128   /* Bit of a vector continuous assignment */
#define vpiNamedEventArray   129   /* multidimensional named event */

/********************** object types added with 1364-2005 *********************/

#define vpiIndexedPartSelect 130   /* Indexed part-select object */
#define vpiGenScopeArray     133   /* array of generated scopes */
#define vpiGenScope          134   /* A generated scope */
#define vpiGenVar            135   /* Object used to instantiate gen scopes */

/*********************************** METHODS **********************************/
/**************** methods used to traverse 1 to 1 relationships ***************/

#define vpiCondition          71   /* condition expression */
#define vpiDelay              72   /* net or gate delay */
#define vpiElseStmt           73   /* else statement */
#define vpiForIncStmt         74   /* increment statement in for loop */
#define vpiForInitStmt        75   /* initialization statement in for loop */
#define vpiHighConn           76   /* higher connection to port */
#define vpiLhs                77   /* left-hand side of assignment */
#define vpiIndex              78   /* index of var select, bit-select, etc. */
#define vpiLeftRange          79   /* left range of vector or part-select */
#define vpiLowConn            80   /* lower connection to port */
#define vpiParent             81   /* parent object */
#define vpiRhs                82   /* right-hand side of assignment */
#define vpiRightRange         83   /* right range of vector or part-select */
#define vpiScope              84   /* containing scope object */
#define vpiSysTfCall          85   /* task function call */
#define vpiTchkDataTerm       86   /* timing check data term */
#define vpiTchkNotifier       87   /* timing check notifier */
#define vpiTchkRefTerm        88   /* timing check reference term */

/************* methods used to traverse 1 to many relationships ***************/

#define vpiArgument           89   /* argument to (system) task/function */
#define vpiBit                90   /* bit of vector net or port */
#define vpiDriver             91   /* driver for a net */
#define vpiInternalScope      92   /* internal scope in module */
#define vpiLoad               93   /* load on net or reg */
#define vpiModDataPathIn      94   /* data terminal of a module path */
#define vpiModPathIn          95   /* Input terminal of a module path */
#define vpiModPathOut         96   /* output terminal of a module path */
#define vpiOperand            97   /* operand of expression */
#define vpiPortInst           98   /* connected port instance */
#define vpiProcess            99   /* process in module, program or interface */
#define vpiVariables         100   /* variables in module */
#define vpiUse               101   /* usage */

/******** methods which can traverse 1 to 1, or 1 to many relationships *******/

#define vpiExpr              102   /* connected expression */
#define vpiPrimitive         103   /* primitive (gate, switch, UDP) */
#define vpiStmt              104   /* statement in process or task */

/************************ methods added with 1364-2001 ************************/

#define vpiActiveTimeFormat  119   /* active $timeformat() system task */
#define vpiInTerm            120   /* To get to a delay device's drivers. */
#define vpiInstanceArray     121   /* vpiInstance arrays */
#define vpiLocalDriver       122   /* local drivers (within a module */
#define vpiLocalLoad         123   /* local loads (within a module */
#define vpiOutTerm           124   /* To get to a delay device's loads. */
#define vpiPorts             125   /* Module port */
#define vpiSimNet            126   /* simulated net after collapsing */
#define vpiTaskFunc          127   /* task/function */

/************************ methods added with 1364-2005 ************************/

#define vpiBaseExpr          131   /* Indexed part-select's base expression */
#define vpiWidthExpr         132   /* Indexed part-select's width expression */

/************************ methods added with 1800-2009 ************************/

#define vpiAutomatics        136   /* Automatic variables of a frame */

/********************************* PROPERTIES *********************************/
/************************** generic object properties *************************/

#define vpiUndefined             -1   /* undefined property */
#define vpiType                   1   /* type of object */
#define vpiName                   2   /* local name of object */
#define vpiFullName               3   /* full hierarchical name */
#define vpiSize                   4   /* size of gate, net, port, etc. */
#define vpiFile                   5   /* File name in which the object is used*/
#define vpiLineNo                 6   /* line number where the object is used */

/***************************** module properties ******************************/

#define vpiTopModule              7   /* top-level module (Boolean) */
#define vpiCellInstance           8   /* cell (Boolean) */
#define vpiDefName                9   /* module definition name */
#define vpiProtected             10   /* source protected module (Boolean) */
#define vpiTimeUnit              11   /* module time unit */
#define vpiTimePrecision         12   /* module time precision */
#define vpiDefNetType            13   /* default net type */
#define vpiUnconnDrive           14   /* unconnected port drive strength */
#define vpiHighZ                   1   /* No default drive given */
#define vpiPull1                   2   /* default pull1 drive */
#define vpiPull0                   3   /* default pull0 drive */
#define vpiDefFile               15   /* File name where the module is defined*/
#define vpiDefLineNo             16   /* line number for module definition */
#define vpiDefDelayMode          47   /* Default delay mode for a module */
#define vpiDelayModeNone           1   /* no delay mode specified */
#define vpiDelayModePath           2   /* path delay mode */
#define vpiDelayModeDistrib        3   /* distributed delay mode */
#define vpiDelayModeUnit           4   /* unit delay mode */
#define vpiDelayModeZero           5   /* zero delay mode */
#define vpiDelayModeMTM            6   /* min:typ:max delay mode */
#define vpiDefDecayTime          48   /* Default decay time for a module */

/*************************** port and net properties **************************/

#define vpiScalar                17   /* scalar (Boolean) */
#define vpiVector                18   /* vector (Boolean) */
#define vpiExplicitName          19   /* port is explicitly named */
#define vpiDirection             20   /* direction of port: */
#define vpiInput                   1   /* input */
#define vpiOutput                  2   /* output */
#define vpiInout                   3   /* inout */
#define vpiMixedIO                 4   /* mixed input-output */
#define vpiNoDirection             5   /* no direction */
#define vpiConnByName            21   /* connected by name (Boolean) */

#define vpiNetType               22   /* net subtypes: */
#define vpiWire                    1   /* wire net */
#define vpiWand                    2   /* wire-and net */
#define vpiWor                     3   /* wire-or net */
#define vpiTri                     4   /* tri net */
#define vpiTri0                    5   /* pull-down net */
#define vpiTri1                    6   /* pull-up net */
#define vpiTriReg                  7   /* three-state reg net */
#define vpiTriAnd                  8   /* three-state wire-and net */
#define vpiTriOr                   9   /* three-state wire-or net */
#define vpiSupply1                10   /* supply-1 net */
#define vpiSupply0                11   /* supply-0 net */
#define vpiNone                   12   /* no default net type (1364-2001) */
#define vpiUwire                  13   /* unresolved wire net (1364-2005) */

#define vpiExplicitScalared      23   /* explicitly scalared (Boolean) */
#define vpiExplicitVectored      24   /* explicitly vectored (Boolean) */
#define vpiExpanded              25   /* expanded vector net (Boolean) */
#define vpiImplicitDecl          26   /* implicitly declared net (Boolean) */
#define vpiChargeStrength        27   /* charge decay strength of net */

/* Defined as part of strengths section.
#define vpiLargeCharge            0x10
#define vpiMediumCharge           0x04
#define vpiSmallCharge            0x02
*/

#define vpiArray                 28   /* variable array (Boolean) */
#define vpiPortIndex             29   /* Port index */

/************************ gate and terminal properties ************************/

#define vpiTermIndex             30   /* Index of a primitive terminal */
#define vpiStrength0             31   /* 0-strength of net or gate */
#define vpiStrength1             32   /* 1-strength of net or gate */
#define vpiPrimType              33   /* primitive subtypes: */
#define vpiAndPrim                 1   /* and gate */
#define vpiNandPrim                2   /* nand gate */
#define vpiNorPrim                 3   /* nor gate */
#define vpiOrPrim                  4   /* or gate */
#define vpiXorPrim                 5   /* xor gate */
#define vpiXnorPrim                6   /* xnor gate */
#define vpiBufPrim                 7   /* buffer */
#define vpiNotPrim                 8   /* not gate */
#define vpiBufif0Prim              9   /* zero-enabled buffer */
#define vpiBufif1Prim             10   /* one-enabled buffer */
#define vpiNotif0Prim             11   /* zero-enabled not gate */
#define vpiNotif1Prim             12   /* one-enabled not gate */
#define vpiNmosPrim               13   /* nmos switch */
#define vpiPmosPrim               14   /* pmos switch */
#define vpiCmosPrim               15   /* cmos switch */
#define vpiRnmosPrim              16   /* resistive nmos switch */
#define vpiRpmosPrim              17   /* resistive pmos switch */
#define vpiRcmosPrim              18   /* resistive cmos switch */
#define vpiRtranPrim              19   /* resistive bidirectional */
#define vpiRtranif0Prim           20   /* zero-enable resistive bidirectional */
#define vpiRtranif1Prim           21   /* one-enable resistive bidirectional */
#define vpiTranPrim               22   /* bidirectional */
#define vpiTranif0Prim            23   /* zero-enabled bidirectional */
#define vpiTranif1Prim            24   /* one-enabled bidirectional */
#define vpiPullupPrim             25   /* pullup */
#define vpiPulldownPrim           26   /* pulldown */
#define vpiSeqPrim                27   /* sequential UDP */
#define vpiCombPrim               28   /* combinational UDP */

/**************** path, path terminal, timing check properties ****************/

#define vpiPolarity              34   /* polarity of module path... */
#define vpiDataPolarity          35   /* ...or data path: */
#define vpiPositive                1   /* positive */
#define vpiNegative                2   /* negative */
#define vpiUnknown                 3   /* unknown (unspecified) */

#define vpiEdge                  36   /* edge type of module path: */
#define vpiNoEdge                  0x00     /* no edge */
#define vpiEdge01                  0x01     /* 0 -> 1 */
#define vpiEdge10                  0x02     /* 1 -> 0 */
#define vpiEdge0x                  0x04     /* 0 -> x */
#define vpiEdgex1                  0x08     /* x -> 1 */
#define vpiEdge1x                  0x10     /* 1 -> x */
#define vpiEdgex0                  0x20     /* x -> 0 */
#define vpiPosedge                 (vpiEdgex1 | vpiEdge01 | vpiEdge0x)
#define vpiNegedge                 (vpiEdgex0 | vpiEdge10 | vpiEdge1x)
#define vpiAnyEdge                 (vpiPosedge | vpiNegedge)

#define vpiPathType              37   /* path delay connection subtypes: */
#define vpiPathFull                1   /* ( a *> b ) */
#define vpiPathParallel            2   /* ( a => b ) */

#define vpiTchkType              38   /* timing check subtypes: */
#define vpiSetup                   1   /* $setup */
#define vpiHold                    2   /* $hold */
#define vpiPeriod                  3   /* $period */
#define vpiWidth                   4   /* $width */
#define vpiSkew                    5   /* $skew */
#define vpiRecovery                6   /* $recovery */
#define vpiNoChange                7   /* $nochange */
#define vpiSetupHold               8   /* $setuphold */
#define vpiFullskew                9   /* $fullskew -- added for 1364-2001 */
#define vpiRecrem                 10   /* $recrem   -- added for 1364-2001 */
#define vpiRemoval                11   /* $removal  -- added for 1364-2001 */
#define vpiTimeskew               12   /* $timeskew -- added for 1364-2001 */

/**************************** expression properties ***************************/

#define vpiOpType                39   /* operation subtypes: */
#define vpiMinusOp                 1   /* unary minus */
#define vpiPlusOp                  2   /* unary plus */
#define vpiNotOp                   3   /* unary not */
#define vpiBitNegOp                4   /* bitwise negation */
#define vpiUnaryAndOp              5   /* bitwise reduction AND */
#define vpiUnaryNandOp             6   /* bitwise reduction NAND */
#define vpiUnaryOrOp               7   /* bitwise reduction OR */
#define vpiUnaryNorOp              8   /* bitwise reduction NOR */
#define vpiUnaryXorOp              9   /* bitwise reduction XOR */
#define vpiUnaryXNorOp            10   /* bitwise reduction XNOR */
#define vpiSubOp                  11   /* binary subtraction */
#define vpiDivOp                  12   /* binary division */
#define vpiModOp                  13   /* binary modulus */
#define vpiEqOp                   14   /* binary equality */
#define vpiNeqOp                  15   /* binary inequality */
#define vpiCaseEqOp               16   /* case (x and z) equality */
#define vpiCaseNeqOp              17   /* case inequality */
#define vpiGtOp                   18   /* binary greater than */
#define vpiGeOp                   19   /* binary greater than or equal */
#define vpiLtOp                   20   /* binary less than */
#define vpiLeOp                   21   /* binary less than or equal */
#define vpiLShiftOp               22   /* binary left shift */
#define vpiRShiftOp               23   /* binary right shift */
#define vpiAddOp                  24   /* binary addition */
#define vpiMultOp                 25   /* binary multiplication */
#define vpiLogAndOp               26   /* binary logical AND */
#define vpiLogOrOp                27   /* binary logical OR */
#define vpiBitAndOp               28   /* binary bitwise AND */
#define vpiBitOrOp                29   /* binary bitwise OR */
#define vpiBitXorOp               30   /* binary bitwise XOR */
#define vpiBitXNorOp              31   /* binary bitwise XNOR */
#define vpiBitXnorOp              vpiBitXNorOp /* added with 1364-2001 */
#define vpiConditionOp            32   /* ternary conditional */
#define vpiConcatOp               33   /* n-ary concatenation */
#define vpiMultiConcatOp          34   /* repeated concatenation */
#define vpiEventOrOp              35   /* event OR */
#define vpiNullOp                 36   /* null operation */
#define vpiListOp                 37   /* list of expressions */
#define vpiMinTypMaxOp            38   /* min:typ:max: delay expression */
#define vpiPosedgeOp              39   /* posedge */
#define vpiNegedgeOp              40   /* negedge */
#define vpiArithLShiftOp          41   /* arithmetic left shift  (1364-2001) */
#define vpiArithRShiftOp          42   /* arithmetic right shift (1364-2001) */
#define vpiPowerOp                43   /* arithmetic power op    (1364-2001) */

#define vpiConstType             40   /* constant subtypes: */
#define vpiDecConst                1   /* decimal integer */
#define vpiRealConst               2   /* real */
#define vpiBinaryConst             3   /* binary integer */
#define vpiOctConst                4   /* octal integer */
#define vpiHexConst                5   /* hexadecimal integer */
#define vpiStringConst             6   /* string literal */
#define vpiIntConst                7   /* integer constant (1364-2001) */
#define vpiTimeConst               8   /* time constant */
#define vpiBlocking              41   /* blocking assignment (Boolean) */
#define vpiCaseType              42   /* case statement subtypes: */
#define vpiCaseExact               1   /* exact match */
#define vpiCaseX                   2   /* ignore X's */
#define vpiCaseZ                   3   /* ignore Z's */
#define vpiNetDeclAssign         43   /* assign part of decl (Boolean) */

/************************** task/function properties **************************/

#define vpiFuncType              44   /* function & system function type */
#define vpiIntFunc                 1   /* returns integer */
#define vpiRealFunc                2   /* returns real */
#define vpiTimeFunc                3   /* returns time */
#define vpiSizedFunc               4   /* returns an arbitrary size */
#define vpiSizedSignedFunc         5   /* returns sized signed value */

/** alias 1364-1995 system function subtypes to 1364-2001 function subtypes ***/

#define vpiSysFuncType             vpiFuncType
#define vpiSysFuncInt              vpiIntFunc
#define vpiSysFuncReal             vpiRealFunc
#define vpiSysFuncTime             vpiTimeFunc
#define vpiSysFuncSized            vpiSizedFunc

#define vpiUserDefn              45   /*user-defined system task/func(Boolean)*/
#define vpiScheduled             46   /* object still scheduled (Boolean) */

/*********************** properties added with 1364-2001 **********************/

#define vpiActive                49   /* reentrant task/func frame is active */
#define vpiAutomatic             50   /* task/func obj is automatic */
#define vpiCell                  51   /* configuration cell */
#define vpiConfig                52   /* configuration config file */
#define vpiConstantSelect        53   /* (Boolean) bit-select or part-select
                                         indices are constant expressions */
#define vpiDecompile             54   /* decompile the object */
#define vpiDefAttribute          55   /* Attribute defined for the obj */
#define vpiDelayType             56   /* delay subtype */
#define vpiModPathDelay            1   /* module path delay */
#define vpiInterModPathDelay       2   /* intermodule path delay */
#define vpiMIPDelay                3   /* module input port delay */
#define vpiIteratorType          57   /* object type of an iterator */
#define vpiLibrary               58   /* configuration library */
#define vpiOffset                60   /* offset from LSB */
#define vpiResolvedNetType       61   /* net subtype after resolution, returns
                                         same subtypes as vpiNetType */
#define vpiSaveRestartID         62   /* unique ID for save/restart data */
#define vpiSaveRestartLocation   63   /* name of save/restart data file */
/* vpiValid,vpiValidTrue,vpiValidFalse were deprecated in 1800-2009 */
#define vpiValid                 64   /* reentrant task/func frame or automatic
                                         variable is valid */
#define vpiValidFalse              0
#define vpiValidTrue               1
#define vpiSigned                65   /* TRUE for vpiIODecl and any object in
                                         the expression class if the object
                                         has the signed attribute */
#define vpiLocalParam            70   /* TRUE when a param is declared as a
                                         localparam */
#define vpiModPathHasIfNone      71   /* Mod path has an ifnone statement */

/*********************** properties added with 1364-2005 **********************/

#define vpiIndexedPartSelectType 72   /* Indexed part-select type */
#define vpiPosIndexed              1   /* +: */
#define vpiNegIndexed              2   /* -: */
#define vpiIsMemory              73   /* TRUE for a one-dimensional reg array */
#define vpiIsProtected           74   /* TRUE for protected design information */

/*************** vpi_control() constants (added with 1364-2001) ***************/

#define vpiStop                  66   /* execute simulator's $stop */
#define vpiFinish                67   /* execute simulator's $finish */
#define vpiReset                 68   /* execute simulator's $reset */
#define vpiSetInteractiveScope   69   /* set simulator's interactive scope */

/**************************** I/O related defines *****************************/

#define VPI_MCD_STDOUT  0x00000001

/*************************** STRUCTURE DEFINITIONS ****************************/

/******************************* time structure *******************************/

typedef struct t_vpi_time
{
  PLI_INT32  type;               /* [vpiScaledRealTime, vpiSimTime,
                                     vpiSuppressTime] */
  PLI_UINT32 high, low;          /* for vpiSimTime */
  double     real;               /* for vpiScaledRealTime */
} s_vpi_time, *p_vpi_time;

/* time types */

#define vpiScaledRealTime 1
#define vpiSimTime        2
#define vpiSuppressTime   3

/****************************** delay structures ******************************/

typedef struct t_vpi_delay
{
  struct t_vpi_time *da;         /* pointer to application-allocated
                                    array of delay values */
  PLI_INT32 no_of_delays;        /* number of delays */
  PLI_INT32 time_type;           /* [vpiScaledRealTime, vpiSimTime,
                                     vpiSuppressTime] */
  PLI_INT32 mtm_flag;            /* true for mtm values */
  PLI_INT32 append_flag;         /* true for append */
  PLI_INT32 pulsere_flag;        /* true for pulsere values */
} s_vpi_delay, *p_vpi_delay;

/***************************** value structures *******************************/

/* vector value */

#ifndef VPI_VECVAL  /* added in 1364-2005 */
#define VPI_VECVAL

typedef struct t_vpi_vecval
{
  /* following fields are repeated enough times to contain vector */
  PLI_UINT32 aval, bval;          /* bit encoding: ab: 00=0, 10=1, 11=X, 01=Z */
} s_vpi_vecval, *p_vpi_vecval;

#endif

/* strength (scalar) value */

typedef struct t_vpi_strengthval
{
  PLI_INT32 logic;               /* vpi[0,1,X,Z] */
  PLI_INT32 s0, s1;              /* refer to strength coding below */
} s_vpi_strengthval, *p_vpi_strengthval;

/* strength values */

#define vpiSupplyDrive     0x80
#define vpiStrongDrive     0x40
#define vpiPullDrive       0x20
#define vpiWeakDrive       0x08
#define vpiLargeCharge     0x10
#define vpiMediumCharge    0x04
#define vpiSmallCharge     0x02
#define vpiHiZ             0x01

/* generic value */

typedef struct t_vpi_value
{
  PLI_INT32 format; /* vpi[[Bin,Oct,Dec,Hex]Str,Scalar,Int,Real,String,
                           Vector,Strength,Suppress,Time,ObjType]Val */
  union
    {
      PLI_BYTE8                *str;       /* string value */
      PLI_INT32                 scalar;    /* vpi[0,1,X,Z] */
      PLI_INT32                 integer;   /* integer value */
      double                    real;      /* real value */
      struct t_vpi_time        *time;      /* time value */
      struct t_vpi_vecval      *vector;    /* vector value */
      struct t_vpi_strengthval *strength;  /* strength value */
      PLI_BYTE8                *misc;      /* ...other */
    } value;
} s_vpi_value, *p_vpi_value;

typedef struct t_vpi_arrayvalue
{
   PLI_UINT32 format; /* vpi[Int,Real,Time,ShortInt,LongInt,ShortReal,
                           RawTwoState,RawFourState]Val */
   PLI_UINT32 flags;  /* array bit flags- vpiUserAllocFlag */
   union
   {
       PLI_INT32 *integers;               /* integer values */
       PLI_INT16 *shortints;              /* short integer values */
       PLI_INT64 *longints;               /* long integer values */
       PLI_BYTE8 *rawvals;                /* 2/4-state vector elements */
       struct t_vpi_vecval *vectors;      /* 4-state vector elements */
       struct t_vpi_time *times;          /* time values */
       double *reals;                     /* real values */
       float *shortreals;                 /* short real values */
   } value;
} s_vpi_arrayvalue, *p_vpi_arrayvalue;

/* value formats */

#define vpiBinStrVal          1
#define vpiOctStrVal          2
#define vpiDecStrVal          3
#define vpiHexStrVal          4
#define vpiScalarVal          5
#define vpiIntVal             6
#define vpiRealVal            7
#define vpiStringVal          8
#define vpiVectorVal          9
#define vpiStrengthVal       10
#define vpiTimeVal           11
#define vpiObjTypeVal        12
#define vpiSuppressVal       13
#define vpiShortIntVal       14
#define vpiLongIntVal        15
#define vpiShortRealVal      16
#define vpiRawTwoStateVal    17
#define vpiRawFourStateVal   18

/* delay modes */

#define vpiNoDelay            1
#define vpiInertialDelay      2
#define vpiTransportDelay     3
#define vpiPureTransportDelay 4

/* force and release flags */

#define vpiForceFlag          5
#define vpiReleaseFlag        6

/* scheduled event cancel flag */

#define vpiCancelEvent        7

/* bit mask for the flags argument to vpi_put_value() */

#define vpiReturnEvent        0x1000

/* bit flags for vpi_get_value_array flags field */

#define vpiUserAllocFlag      0x2000

/* bit flags for vpi_put_value_array flags field */

#define vpiOneValue           0x4000
#define vpiPropagateOff       0x8000

/* scalar values */

#define vpi0                  0
#define vpi1                  1
#define vpiZ                  2
#define vpiX                  3
#define vpiH                  4
#define vpiL                  5
#define vpiDontCare           6
/*
#define vpiNoChange           7   Defined under vpiTchkType, but
                                  can be used here.
*/

/*********************** system task/function structure ***********************/

typedef struct t_vpi_systf_data
{
  PLI_INT32 type;                       /* vpiSysTask, vpiSysFunc */
  PLI_INT32 sysfunctype;                /* vpiSysTask, vpi[Int,Real,Time,Sized,
                                                           SizedSigned]Func */
  PLI_BYTE8 *tfname;                    /* first character must be '$' */
  PLI_INT32 (*calltf)(PLI_BYTE8 *);
  PLI_INT32 (*compiletf)(PLI_BYTE8 *);
  PLI_INT32 (*sizetf)(PLI_BYTE8 *);     /* for sized function callbacks only */
  PLI_BYTE8 *user_data;
} s_vpi_systf_data, *p_vpi_systf_data;

#define vpiSysTask            1
#define vpiSysFunc            2

/* the subtypes are defined under the vpiFuncType property */

/**************** SystemVerilog execution information structure ***************/

typedef struct t_vpi_vlog_info
{
  PLI_INT32 argc;
  PLI_BYTE8 **argv;
  PLI_BYTE8 *product;
  PLI_BYTE8 *version;
} s_vpi_vlog_info, *p_vpi_vlog_info;

/*********************** PLI error information structure **********************/

typedef struct t_vpi_error_info
{
  PLI_INT32 state;           /* vpi[Compile,PLI,Run] */
  PLI_INT32 level;           /* vpi[Notice,Warning,Error,System,Internal] */
  PLI_BYTE8 *message;
  PLI_BYTE8 *product;
  PLI_BYTE8 *code;
  PLI_BYTE8 *file;
  PLI_INT32 line;
} s_vpi_error_info, *p_vpi_error_info;

/* state when error occurred */

#define vpiCompile              1
#define vpiPLI                  2
#define vpiRun                  3

/* error severity levels */

#define vpiNotice               1
#define vpiWarning              2
#define vpiError                3
#define vpiSystem               4
#define vpiInternal             5

/**************************** callback structures *****************************/

/* normal callback structure */

typedef struct t_cb_data
{
  PLI_INT32    reason;                        /* callback reason */
  PLI_INT32    (*cb_rtn)(struct t_cb_data *); /* call routine */
  vpiHandle    obj;                           /* trigger object */
  p_vpi_time   time;                          /* callback time */
  p_vpi_value  value;                         /* trigger object value */
  PLI_INT32    index;                         /* index of the memory word or
                                                 var select that changed */
  PLI_BYTE8   *user_data;
} s_cb_data, *p_cb_data;

/****************************** CALLBACK REASONS ******************************/

/***************************** Simulation related *****************************/

#define cbValueChange             1
#define cbStmt                    2
#define cbForce                   3
#define cbRelease                 4

/******************************** Time related ********************************/

#define cbAtStartOfSimTime        5
#define cbReadWriteSynch          6
#define cbReadOnlySynch           7
#define cbNextSimTime             8
#define cbAfterDelay              9

/******************************* Action related *******************************/

#define cbEndOfCompile           10
#define cbStartOfSimulation      11
#define cbEndOfSimulation        12
#define cbError                  13
#define cbTchkViolation          14
#define cbStartOfSave            15
#define cbEndOfSave              16
#define cbStartOfRestart         17
#define cbEndOfRestart           18
#define cbStartOfReset           19
#define cbEndOfReset             20
#define cbEnterInteractive       21
#define cbExitInteractive        22
#define cbInteractiveScopeChange 23
#define cbUnresolvedSystf        24

/**************************** Added with 1364-2001 ****************************/

#define cbAssign                 25
#define cbDeassign               26
#define cbDisable                27
#define cbPLIError               28
#define cbSignal                 29

/**************************** Added with 1364-2005 ****************************/
#define cbNBASynch               30
#define cbAtEndOfSimTime         31

/**************************** FUNCTION DECLARATIONS ***************************/

/* Include compatibility mode macro definitions. */
//#include "vpi_compatibility.h"

/* callback related */

XXTERN vpiHandle    vpi_register_cb     PROTO_PARAMS((p_cb_data cb_data_p));
XXTERN PLI_INT32    vpi_remove_cb       PROTO_PARAMS((vpiHandle cb_obj));
XXTERN void         vpi_get_cb_info     PROTO_PARAMS((vpiHandle object,
                                                      p_cb_data cb_data_p));
XXTERN vpiHandle    vpi_register_systf  PROTO_PARAMS((p_vpi_systf_data
                                                      systf_data_p));
XXTERN void         vpi_get_systf_info  PROTO_PARAMS((vpiHandle object,
                                                      p_vpi_systf_data
                                                      systf_data_p));

/* for obtaining handles */

XXTERN vpiHandle    vpi_handle_by_name  PROTO_PARAMS((PLI_BYTE8    *name,
                                                      vpiHandle    scope));
XXTERN vpiHandle    vpi_handle_by_index PROTO_PARAMS((vpiHandle    object,
                                                      PLI_INT32    indx));

/* for traversing relationships */

XXTERN vpiHandle    vpi_handle          PROTO_PARAMS((PLI_INT32   type,
                                                      vpiHandle   refHandle));
XXTERN vpiHandle    vpi_handle_multi    PROTO_PARAMS((PLI_INT32   type,
                                                      vpiHandle   refHandle1,
                                                      vpiHandle   refHandle2,
                                                      ... ));
XXTERN vpiHandle    vpi_iterate         PROTO_PARAMS((PLI_INT32   type,
                                                      vpiHandle   refHandle));
XXTERN vpiHandle    vpi_scan            PROTO_PARAMS((vpiHandle   iterator));

/* for processing properties */

XXTERN PLI_INT32    vpi_get             PROTO_PARAMS((PLI_INT32   property,
                                                      vpiHandle   object));
XXTERN PLI_INT64    vpi_get64           PROTO_PARAMS((PLI_INT32   property,
                                                      vpiHandle   object));
XXTERN PLI_BYTE8   *vpi_get_str         PROTO_PARAMS((PLI_INT32   property,
                                                      vpiHandle   object));

/* delay processing */

XXTERN void         vpi_get_delays      PROTO_PARAMS((vpiHandle object,
                                                      p_vpi_delay delay_p));
XXTERN void         vpi_put_delays      PROTO_PARAMS((vpiHandle object,
                                                      p_vpi_delay delay_p));

/* value processing */

XXTERN void         vpi_get_value       PROTO_PARAMS((vpiHandle expr,
                                                      p_vpi_value value_p));
XXTERN vpiHandle    vpi_put_value       PROTO_PARAMS((vpiHandle object,
                                                      p_vpi_value value_p,
                                                      p_vpi_time time_p,
                                                      PLI_INT32 flags));
XXTERN void         vpi_get_value_array PROTO_PARAMS((vpiHandle object,
                                                      p_vpi_arrayvalue arrayvalue_p,
                                                      PLI_INT32 *index_p,
                                                      PLI_UINT32 num));
XXTERN void         vpi_put_value_array PROTO_PARAMS((vpiHandle object,
                                                      p_vpi_arrayvalue arrayvalue_p,
                                                      PLI_INT32 *index_p,
                                                      PLI_UINT32 num));

/* time processing */

XXTERN void         vpi_get_time        PROTO_PARAMS((vpiHandle object,
                                                      p_vpi_time time_p));

/* I/O routines */

XXTERN PLI_UINT32   vpi_mcd_open        PROTO_PARAMS((PLI_BYTE8 *fileName));
XXTERN PLI_UINT32   vpi_mcd_close       PROTO_PARAMS((PLI_UINT32 mcd));
XXTERN PLI_BYTE8   *vpi_mcd_name        PROTO_PARAMS((PLI_UINT32 cd));
XXTERN PLI_INT32    vpi_mcd_printf      PROTO_PARAMS((PLI_UINT32 mcd,
                                                      PLI_BYTE8 *format,
                                                      ...));
XXTERN PLI_INT32    vpi_printf          PROTO_PARAMS((PLI_BYTE8 *format,
                                                      ...));

/* utility routines */

XXTERN PLI_INT32    vpi_compare_objects PROTO_PARAMS((vpiHandle object1,
                                                      vpiHandle object2));
XXTERN PLI_INT32    vpi_chk_error       PROTO_PARAMS((p_vpi_error_info
                                                      error_info_p));
/* vpi_free_object() was deprecated in 1800-2009 */
XXTERN PLI_INT32    vpi_free_object     PROTO_PARAMS((vpiHandle object));
XXTERN PLI_INT32    vpi_release_handle  PROTO_PARAMS((vpiHandle object));
XXTERN PLI_INT32    vpi_get_vlog_info   PROTO_PARAMS((p_vpi_vlog_info
                                                      vlog_info_p));

/* routines added with 1364-2001 */

XXTERN PLI_INT32    vpi_get_data        PROTO_PARAMS((PLI_INT32 id,
                                                      PLI_BYTE8 *dataLoc,
                                                      PLI_INT32 numOfBytes));
XXTERN PLI_INT32    vpi_put_data        PROTO_PARAMS((PLI_INT32 id,
                                                      PLI_BYTE8 *dataLoc,
                                                      PLI_INT32 numOfBytes));
XXTERN void        *vpi_get_userdata    PROTO_PARAMS((vpiHandle obj));
XXTERN PLI_INT32    vpi_put_userdata    PROTO_PARAMS((vpiHandle obj,
                                                      void *userdata));
XXTERN PLI_INT32    vpi_vprintf         PROTO_PARAMS((PLI_BYTE8 *format,
                                                      va_list ap));
XXTERN PLI_INT32    vpi_mcd_vprintf     PROTO_PARAMS((PLI_UINT32 mcd,
                                                      PLI_BYTE8 *format,
                                                      va_list ap));
XXTERN PLI_INT32    vpi_flush           PROTO_PARAMS((void));
XXTERN PLI_INT32    vpi_mcd_flush       PROTO_PARAMS((PLI_UINT32 mcd));
XXTERN PLI_INT32    vpi_control         PROTO_PARAMS((PLI_INT32 operation,
                                                      ...));
XXTERN vpiHandle    vpi_handle_by_multi_index PROTO_PARAMS((vpiHandle obj,
                                                      PLI_INT32 num_index,
                                                      PLI_INT32 *index_array));

/****************************** GLOBAL VARIABLES ******************************/

PLI_VEXTERN PLI_DLLESPEC void (*vlog_startup_routines[])( void );

  /* array of function pointers, last pointer should be null */

#undef PLI_EXTERN
#undef PLI_VEXTERN

#ifdef VPI_USER_DEFINED_DLLISPEC
# undef VPI_USER_DEFINED_DLLISPEC
# undef PLI_DLLISPEC
#endif
#ifdef VPI_USER_DEFINED_DLLESPEC
# undef VPI_USER_DEFINED_DLLESPEC
# undef PLI_DLLESPEC
#endif

#ifdef PLI_PROTOTYPES
# undef PLI_PROTOTYPES
# undef PROTO_PARAMS
# undef XXTERN
# undef EETERN
#endif

#ifdef __cplusplus
}
#endif

#endif /* VPI_USER_H */
