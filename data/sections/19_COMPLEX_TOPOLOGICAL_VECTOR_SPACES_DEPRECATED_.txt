###############################################################################
  COMPLEX TOPOLOGICAL VECTOR SPACES (DEPRECATED)
###############################################################################
The intent is for this deprecated section to be deleted once its theorems
  have extensible structure versions (or are not useful).  You can make a list
  of "terminal" theorems (i.e., theorems not referenced by anything else) and
  for each theorem see if there exists an extensible structure version (or
  decide it is not useful), and if so, delete it.  Then, repeat this
  recursively.  One way to search for terminal theorems is to log the output
  ("MM> OPEN LOG xxx.txt") of "MM> SHOW USAGE <label-match>" in the Metamath
  program and search for "(None)".

$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Additional material on group theory (deprecated)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  This section contains an earlier development of groups that was defined
  before extensible structures were introduced.

  The intent is for this deprecated section to be deleted once the
  corresponding definitions and theorems for complex topological vector spaces,
  which are using them, are revised accordingly.

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definitions and basic properties for groups
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c GrpOp $.
  $c GId $.
  $c inv $.
  $c /g $.

  $( Extend class notation with the class of all group operations. $)
  cgr $a class GrpOp $.

  $( Extend class notation with a function mapping a group operation to the
     group's identity element. $)
  cgi $a class GId $.

  $( Extend class notation with a function mapping a group operation to the
     inverse function for the group. $)
  cgn $a class inv $.

  $( Extend class notation with a function mapping a group operation to the
     division (or subtraction) operation for the group. $)
  cgs $a class /g $.

  ${
    $d g t u x y z $.
    $( Define the class of all group operations.  The base set for a group can
       be determined from its group operation.  Based on the definition in
       Exercise 28 of [Herstein] p. 54.  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    df-grpo $a |- GrpOp = { g | E. t ( g : ( t X. t ) --> t
       /\ A. x e. t A. y e. t A. z e. t ( ( x g y ) g z ) = ( x g ( y g z ) )
   /\ E. u e. t A. x e. t ( ( u g x ) = x /\ E. y e. t ( y g x ) = u ) ) } $.

    $( Define a function that maps a group operation to the group's identity
       element.  (Contributed by FL, 5-Feb-2010.)  (Revised by Mario Carneiro,
       15-Dec-2013.)  (New usage is discouraged.) $)
    df-gid $a |- GId = ( g e. _V |-> ( iota_ u e. ran g A. x e. ran g
                        ( ( u g x ) = x /\ ( x g u ) = x ) ) ) $.

    $( Define a function that maps a group operation to the group's inverse
       function.  (Contributed by NM, 26-Oct-2006.)
       (New usage is discouraged.) $)
    df-ginv $a |- inv = ( g e. GrpOp |-> ( x e. ran g |->
                    ( iota_ z e. ran g ( z g x ) = ( GId ` g ) ) ) ) $.

    $( Define a function that maps a group operation to the group's division
       (or subtraction) operation.  (Contributed by NM, 15-Feb-2008.)
       (New usage is discouraged.) $)
    df-gdiv $a |- /g = ( g e. GrpOp |-> ( x e. ran g , y e. ran g |->
                         ( x g ( ( inv ` g ) ` y ) ) ) ) $.
  $}

  ${
    $d g t u x y z G $.  $d g t u x y z X $.
    isgrp.1 $e |- X = ran G $.
    $( The predicate "is a group operation."  Note that ` X ` is the base set
       of the group.  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    isgrpo $p |- ( G e. A -> ( G e. GrpOp <-> ( G : ( X X. X ) --> X /\
       A. x e. X A. y e. X A. z e. X ( ( x G y ) G z ) = ( x G ( y G z ) )
   /\ E. u e. X A. x e. X ( ( u G x ) = x /\ E. y e. X ( y G x ) = u ) ) ) ) $=
      ( vt vg wcel cv wceq cxp wf co wral wrex wa oveq cgr crn w3a oveq1d eqtrd
      wex feq1 oveq2d eqeq12d ralbidv 2ralbidv eqeq1d rexbidv anbi12d 3anbi123d
      rexralbidv exbidv df-grpo elab2g simpl ralimi oveq2 id eqcom bitrdi rspcv
      wfo rspceeqv syld syl5 reximdv impcom ralrimiva anim2i foov sylibr eqcomd
      ex forn syl 3adant2 pm4.71ri exbii wb rnexg eqeq2i xpeq1 xpeq2 feq2d feq3
      cvv bitrd raleq raleqbi1dv rexeq anbi2d rexeqbi1dv sylbir ceqsexgv ) FEKZ
      FUAKZILZFUBZMZXBXBNZXBFOZALZBLZFPZCLZFPZXGXHXJFPZFPZMZCXBQZBXBQZAXBQZDLZX
      GFPZXGMZXHXGFPZXRMZBXBRZSZAXBQZDXBRZUCZSZIUFZGGNZGFOZXNCGQZBGQZAGQZXTYBBG
      RZSZAGQZDGRZUCZWTXAYGIUFZYIXEXBJLZOZXGXHUUAPZXJUUAPZXGXHXJUUAPZUUAPZMZCXB
      QZBXBQAXBQZXRXGUUAPZXGMZXHXGUUAPZXRMZBXBRZSZAXBQDXBRZUCZIUFYTJFUAEUUAFMZU
      UQYGIUURUUBXFUUIXQUUPYFXEXBUUAFUGUURUUHXOABXBXBUURUUGXNCXBUURUUDXKUUFXMUU
      RUUDUUCXJFPXKUUCXJUUAFTUURUUCXIXJFXGXHUUAFTUDUEUURUUFXGUUEFPXMXGUUEUUAFTU
      URUUEXLXGFXHXJUUAFTUHUEUIUJUKUURUUOYDDAXBXBUURUUKXTUUNYCUURUUJXSXGXRXGUUA
      FTULUURUUMYBBXBUURUULYAXRXHXGUUAFTULUMUNUPUOUQABCDIJURUSYGYHIYGXDXFYFXDXQ
      XFYFSZXEXBFVGZXDUUSXFXJXRXHFPZMBXBRZDXBRZCXBQZSUUTYFUVDXFYFUVCCXBXJXBKZYF
      UVCUVEYEUVBDXBYEXTAXBQZUVEUVBYDXTAXBXTYCUTVAUVEUVFXJXRXJFPZMZUVBXTUVHAXJX
      BXGXJMZXTUVGXJMUVHUVIXSUVGXGXJXGXJXRFVBUVIVCUIUVGXJVDVEVFUVEUVHUVBBXJXBUV
      AUVGXJXHXJXRFVBVHVRVIVJVKVLVMVNDBCXBXBXBFVOVPUUTXCXBXEXBFVSVQVTWAWBWCVEWT
      XCWKKYIYSWDFEWEYGYSIXCWKXDXBGMZYGYSWDGXCXBHWFUVJXFYKXQYNYFYRUVJXFYJXBFOYK
      UVJXEYJXBFUVJXEGXBNYJXBGXBWGXBGGWHUEWIXBGYJFWJWLXPYMAXBGXOYLBXBGXNCXBGWMW
      NWNYEYQDXBGYDYPAXBGUVJYCYOXTYBBXBGWOWPWNWQUOWRWSVTWL $.
  $}

  ${
    $d u x y z G $.  $d u x y z U $.  $d u x y z X $.  $d y N $.
    isgrpoi.1 $e |- X e. _V $.
    isgrpoi.2 $e |- G : ( X X. X ) --> X $.
    isgrpoi.3 $e |- ( ( x e. X /\ y e. X /\ z e. X ) ->
                   ( ( x G y ) G z ) = ( x G ( y G z ) ) ) $.
    isgrpoi.4 $e |- U e. X $.
    isgrpoi.5 $e |- ( x e. X -> ( U G x ) = x ) $.
    isgrpoi.6 $e |- ( x e. X -> N e. X ) $.
    isgrpoi.7 $e |- ( x e. X -> ( N G x ) = U ) $.
    $( Properties that determine a group operation.  Read ` N ` as
       ` N ( x ) ` .  (Contributed by NM, 4-Nov-2006.)
       (New usage is discouraged.) $)
    isgrpoi $p |- G e. GrpOp $=
      ( vu wcel co wceq wral wrex cgr cxp wf cv rgen3 eqeq1d rspcev syl2anc jca
      wa oveq1 rgen eqeq2 rexbidv anbi12d ralbidv mp2an cvv w3a wb xpex fex crn
      wfo eqcomd rspceov mp3an1 mpdan foov mpbir2an forn eqcomi isgrpo mpbir3an
      ax-mp ) EUAPZGGUBZGEUCZAUDZBUDZEQCUDZEQVSVTWAEQZEQRZCGSBGSAGSZOUDZVSEQZVS
      RZVTVSEQZWERZBGTZUJZAGSZOGTZIWCABCGGGJUEDGPZDVSEQZVSRZWHDRZBGTZUJZAGSZWMK
      WSAGVSGPZWPWRLXAFGPFVSEQZDRZWRMNWQXCBFGVTFRWHXBDVTFVSEUKUFUGUHUIULWLWTODG
      WEDRZWKWSAGXDWGWPWJWRXDWFWOVSWEDVSEUKUFXDWIWQBGWEDWHUMUNUOUPUGUQEURPZVPVR
      WDWMUSUTVRVQURPXEIGGHHVAVQGUREVBUQABCOUREGEVCZGVQGEVDZXFGRXGVRVSWBRCGTBGT
      ZAGSIXHAGXAVSWORZXHXAWOVSLVEWNXAXIXHKBCGGDVSVSEVFVGVHULBCAGGGEVIVJVQGEVKV
      OVLVMVOVN $.
  $}

  ${
    $d w x y z A $.  $d x y z B $.  $d z C $.  $d u w x y z G $.
    $d u w x y z X $.  $d y U $.
    grpfo.1 $e |- X = ran G $.
    $( A group operation maps onto the group's underlying set.  (Contributed by
       NM, 30-Oct-2006.)  (New usage is discouraged.) $)
    grpofo $p |- ( G e. GrpOp -> G : ( X X. X ) -onto-> X ) $=
      ( vx vy vz vu cgr wcel cxp wf crn wceq wa wfo cv co wral wrex w3a isgrpo
      ibi simp1d eqcomi jctir dffo2 sylibr ) AHIZBBJZBAKZALZBMZNUIBAOUHUJULUHUJ
      DPZEPZAQFPZAQUMUNUOAQAQMFBREBRDBRZGPZUMAQUMMUNUMAQUQMEBSNDBRGBSZUHUJUPURT
      DEFGHABCUAUBUCBUKCUDUEUIBAUFUG $.

    $( Closure law for a group operation.  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    grpocl $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( A G B ) e. X ) $=
      ( cgr wcel cxp wf co wfo grpofo fof syl fovcdm syl3an1 ) CFGZDDHZDCIZADGB
      DGABCJDGQRDCKSCDELRDCMNABDDDCOP $.

    $( A group has a left identity element, and every member has a left
       inverse.  (Contributed by NM, 2-Nov-2006.)
       (New usage is discouraged.) $)
    grpolidinv $p |- ( G e. GrpOp ->
         E. u e. X A. x e. X ( ( u G x ) = x /\ E. y e. X ( y G x ) = u ) ) $=
      ( vz cgr wcel cxp wf cv co wceq wral wrex wa w3a isgrpo ibi simp3d ) DHIZ
      EEJEDKZALZBLZDMGLZDMUDUEUFDMDMNGEOBEOAEOZCLZUDDMUDNUEUDDMUHNBEPQAEOCEPZUB
      UCUGUIRABGCHDEFSTUA $.

    $( The base set of a group is not empty.  (Contributed by Szymon
       Jaroszewicz, 3-Apr-2007.)  (New usage is discouraged.) $)
    grpon0 $p |- ( G e. GrpOp -> X =/= (/) ) $=
      ( vu vx vy cgr wcel cv co wceq wrex wa wral c0 wne grpolidinv rexn0 syl )
      AGHDIZEIZAJUAKFIUAAJTKFBLMEBNZDBLBOPEFDABCQUBDBRS $.

    $( A group operation is associative.  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    grpoass $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
              ( ( A G B ) G C ) = ( A G ( B G C ) ) ) $=
      ( vx vy vz vu cgr wcel cv co wceq wral w3a oveq1 eqeq12d oveq2 wf wrex wa
      cxp isgrpo ibi simp2d oveq1d oveq2d rspc3v mpan9 ) DKLZGMZHMZDNZIMZDNZUMU
      NUPDNZDNZOZIEPHEPGEPZAELBELCELQABDNZCDNZABCDNZDNZOZULEEUDEDUAZVAJMZUMDNUM
      OUNUMDNVHOHEUBUCGEPJEUBZULVGVAVIQGHIJKDEFUEUFUGUTVFAUNDNZUPDNZAURDNZOVBUP
      DNZABUPDNZDNZOGHIABCEEEUMAOZUQVKUSVLVPUOVJUPDUMAUNDRUHUMAURDRSUNBOZVKVMVL
      VOVQVJVBUPDUNBADTUHVQURVNADUNBUPDRUISUPCOZVMVCVOVEUPCVBDTVRVNVDADUPCBDTUI
      SUJUK $.

    $( Lemma for ~ grpoidinv .  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    grpoidinvlem1 $p |- ( ( ( G e. GrpOp /\ ( Y e. X /\ A e. X ) ) /\
                  ( ( Y G A ) = U /\ ( A G A ) = A ) ) -> ( U G A ) = U ) $=
      ( cgr wcel wa co wceq w3a id 3anidm23 grpoass sylan2 oveq1 ad2antrl oveq2
      adantr ad2antll simprl eqtrd 3eqtr3d ) CGHZEDHZADHZIZIZEACJZBKZAACJZAKZIZ
      IZUJACJZEULCJZBACJZBUIUPUQKZUNUHUEUFUGUGLZUSUFUGUTUTMNEAACDFOPTUKUPURKUIU
      MUJBACQRUOUQUJBUMUQUJKUIUKULAECSUAUIUKUMUBUCUD $.

    $( Lemma for ~ grpoidinv .  (Contributed by NM, 10-Oct-2006.)
       (New usage is discouraged.) $)
    grpoidinvlem2 $p |- ( ( ( G e. GrpOp /\ ( Y e. X /\ A e. X ) )
     /\ ( ( U G Y ) = Y /\ ( Y G A ) = U ) )
            -> ( ( A G Y ) G ( A G Y ) ) = ( A G Y ) ) $=
      ( cgr wcel wa co wceq w3a simprr simprl grpocl 3com23 3jca grpoass syldan
      3expb adantr oveq1 adantl simpl eqtr2d id 3anidm13 sylan2 sylan9eqr eqtrd
      eqcomd oveq2d ) CGHZEDHZADHZIZIZBECJZEKZEACJZBKZIZIZAECJZVDCJZAEVDCJZCJZV
      DUQVEVGKZVBUMUPUOUNVDDHZLVHUQUOUNVIUMUNUOMUMUNUONUMUNUOVIUMUOUNVIAECDFOPT
      QAEVDCDFRSUAVCVFEACVCEVFVBUQEUTECJZVFVBVJUREVAVJURKUSUTBECUBUCUSVAUDUEUPU
      MUNUOUNLZVJVFKUNUOVKVKUFUGEAECDFRUHUIUKULUJ $.

    ${
      $d w x y z U $.  $d w y ph $.  $d y ps $.
      grpidinvlem3.2 $e |- ( ph <-> A. x e. X ( U G x ) = x ) $.
      grpidinvlem3.3 $e |- ( ps <-> A. x e. X E. z e. X ( z G x ) = U ) $.
      $( Lemma for ~ grpoidinv .  (Contributed by NM, 11-Oct-2006.)
         (New usage is discouraged.) $)
      grpoidinvlem3 $p |- ( ( ( ( G e. GrpOp /\ U e. X ) /\ ( ph /\ ps ) ) /\
                  A e. X ) -> E. y e. X ( ( y G A ) = U /\ ( A G y ) = U ) ) $=
        ( vw wcel wa cv co wceq wrex wral cgr oveq1 eqeq1d cbvrexvw bitri oveq2
        ralbii rexbidv rspccva sylanb adantll grpocl adantllr ad2antrl ad2antrr
        3expa biimpi eqeq12d rspcva syl2anc adantr pm3.22 an31s adantlll anim1i
        id adantlr grpoidinvlem2 3expb ad2ant2rl sylan2b anass an32s syldan imp
        wi grpoidinvlem1 sylan exp43 rexlimdv syl5 mpand exp32 com34 imp32 impl
        ex mpd eqtr3d ancld reximdva ) HUANZGINZOZABOZOZFINZOZDPZFHQZGRZDISZXAF
        WSHQZGRZOZDISWOWQXBWNBWQXBABWSCPZHQZGRZDISZCITZWQXBBEPZXFHQZGRZEISZCITZ
        XJLXNXICIXMXHEDIXKWSRXLXGGXKWSXFHUBUCUDUGUEXIXBCFIXFFRZXHXADIXPXGWTGXFF
        WSHUFUCUHUIUJUKUKWRXAXEDIWRWSINZOZXAXDXRXAXDXRXAOZGXCHQZXCGXRXTXCRZXAXR
        XCINZGXFHQZXFRZCITZYAWNWQXQYBWOWLWQXQYBWMWLWQXQYBFWSHIJULZUPUMUMWPYEWQX
        QAYEWNBAYEKUQUNUOYDYACXCIXFXCRZYCXTXFXCXFXCGHUFYGVFURUSUTVAXSXCXCHQXCRZ
        XTGRZXSWLXQWQOZOZGWSHQZWSRZXAOYHXRYKXAWNWQXQYKWOWLWQXQYKWMXQWQWLYKYJWLV
        BVCUMUMVAXRYMXAWOWQXQYMWNWOXQYMWQAXQYMBAYEXQYMKYDYMCWSIXFWSRZYCYLXFWSXF
        WSGHUFYNVFURUIUJVGVGVDVEFGHIWSJVHUTXRYHYIVPZXAWPWQXQYOWNABWQXQOZYOVPWNA
        YPBYOWNAYPBYOVPWNAYPOOZYBBYOWLYPYBWMAWLWQXQYBYFVIZVJYBBOMPZXCHQZGRZMISZ
        YQYOBYBYSXFHQZGRZMISZCITZUUBBXOUUFLXNUUECIXMUUDEMIXKYSRXLUUCGXKYSXFHUBU
        CUDUGUEUUEUUBCXCIYGUUDUUAMIYGUUCYTGXFXCYSHUFUCUHUSVKYQUUAYOMIYQYSINZUUA
        YHYIYQUUGOWLUUGYBOOZUUAYHOYIYQUUGUUHWLYPUUGUUHVPZWMAWLYPYBUUIYRWLYBOUUG
        UUHWLUUGYBUUHWLUUGOYBOUUHWLUUGYBVLUQVMWGVNVJVOXCGHIYSJVQVRVSVTWAWBWCWDW
        EWFVAWHWIWGWJWKWH $.
    $}

    $( Lemma for ~ grpoidinv .  (Contributed by NM, 14-Oct-2006.)
       (New usage is discouraged.) $)
    grpoidinvlem4 $p |- ( ( ( G e. GrpOp /\ A e. X ) /\ E. y e. X
             ( ( y G A ) = U /\ ( A G y ) = U ) ) -> ( A G U ) = ( U G A ) ) $=
      ( cgr wcel wa cv wceq simpll simplr simpr grpoass syl13anc oveq2 sylan9eq
      co oveq1 sylan9req anasss r19.29an ) DGHZBEHZIZAJZBDSZCKZBUGDSZCKZIBCDSZC
      BDSZKZAEUFUGEHZIZUIUKUNUPUIIUKULUJBDSZUMUPUIUQBUHDSZULUPUDUEUOUEUQURKUDUE
      UOLUDUEUOMZUFUONUSBUGBDEFOPUHCBDQRUJCBDTUAUBUC $.

    $( A group has a left and right identity element, and every member has a
       left and right inverse.  (Contributed by NM, 14-Oct-2006.)
       (New usage is discouraged.) $)
    grpoidinv $p |- ( G e. GrpOp -> E. u e. X A. x e. X ( ( ( u G x ) = x /\
         ( x G u ) = x ) /\ E. y e. X ( ( y G x ) = u /\ ( x G y ) = u ) ) ) $=
      ( vz vw wcel cv co wceq wrex wa wral simpl ralimi id adantll adantl oveq2
      cgr eqeq12d rspccva sylan anim1i adantrr adantr ad2antlr simpr jca32 biid
      grpoidinvlem3 sylancom grpoidinvlem4 eqtrd ralrimiva grpolidinv reximddv
      syl2anc jca31 ) DUBIZCJZGJZDKZVDLZHJVDDKVCLHEMZNZGEOZVCAJZDKZVJLZVJVCDKZV
      JLZNBJZVJDKVCLVJVODKVCLNBEMZNZAEOCEVBVCEIZVINZNZVQAEVTVJEIZNZVLVNVPVSWAVL
      VBVIWAVLVRVIVFGEOZWAVLVHVFGEVFVGPQZVFVLGVJEVDVJLZVEVKVDVJVDVJVCDUAWERUCUD
      UESSZWBVMVKVJWBVBWANVPVMVKLVTVBWAVBVSPUFVTWAVBVRNZWCVGGEOZNNVPWBWGWCWHVTW
      GWAVBVRWGVIWGRUGUHVSWCVBWAVIWCVRWDTUIVSWHVBWAVIWHVRVHVGGEVFVGUJQTUIUKWCWH
      GBHVJVCDEFWCULWHULUMUNZBVJVCDEFUOUTWFUPWIVAUQGHCDEFURUS $.

    $( The left identity element of a group is unique.  Lemma 2.2.1(a) of
       [Herstein] p. 55.  (Contributed by NM, 14-Oct-2006.)
       (New usage is discouraged.) $)
    grpoideu $p |- ( G e. GrpOp -> E! u e. X A. x e. X ( u G x ) = x ) $=
      ( vw vz vy wcel cv co wceq wral weq wa wrex oveq2 id eqeq12d eqeq1d sylib
      cgr wi wreu grpoidinv simpll ralimi cbvralvw ad2antlr simpr oveq1 anbi12d
      adantl rexbidv rspcva adantll sylan2 grpoidinvlem4 syldan adantllr adantr
      an32s ad2ant2rl ad2ant2lr 3eqtr3d ex mpand ralrimiva jca reximdva ralbidv
      mpd reu8 sylibr ) CUBIZBJZAJZCKZVQLZADMZFJZVQCKZVQLZADMZBFNZUCZFDMZOZBDPZ
      VTBDUDVOVPGJZCKZWJLZWJVPCKWJLZOZHJZWJCKZVPLZWJWOCKZVPLZOZHDPZOZGDMZBDPWIG
      HBCDEUEVOXCWHBDVOVPDIZOZXCWHXEXCOZVTWGXCVTXEXCWLGDMVTXBWLGDWLWMXAUFUGWLVS
      GADGANZWKVRWJVQWJVQVPCQXGRSUHUAZUMXFWFFDXFWADIZOZVTWDWEXCVTXEXIXHUIXJVTWD
      OZWEXJXKOWAVPCKZVPWACKZVPWAXJXLXMLZXKVOXCXIXNXDVOXIXCXNVOXIOZXCWOWACKZVPL
      ZWAWOCKZVPLZOZHDPZXNXCXOXAGDMZYAXBXAGDWNXAUJUGXIYBYAVOXAYAGWADGFNZWTXTHDY
      CWQXQWSXSYCWPXPVPWJWAWOCQTYCWRXRVPWJWAWOCUKTULUNUOUPUQHWAVPCDEURUSVBUTVAX
      EXIXKXLVPLZXCXEWDYDXIVTXDWDYDVOWCYDAVPDABNZWBXLVQVPVQVPWACQYERSUOUPVCUTXI
      VTXMWALZXFWDVSYFAWADAFNZVRXMVQWAVQWAVPCQYGRSUOVDVEVFVGVHVIVFVJVLVTWDBFDWE
      VSWCADWEVRWBVQVPWAVQCUKTVKVMVN $.
  $}

  $( A group's range in terms of its domain.  (Contributed by NM, 6-Apr-2008.)
     (New usage is discouraged.) $)
  grporndm $p |- ( G e. GrpOp -> ran G = dom dom G ) $=
    ( cgr wcel crn cxp wfo cdm wceq eqid grpofo fof fdmd dmeqd dmxpid eqtr2di
    syl ) ABCADZQEZQAFZQAGZGZHAQQIJSUARGQSTRSRQARQAKLMQNOP $.

  $( The empty set is not a group.  (Contributed by NM, 25-Apr-2007.)
     (New usage is discouraged.) $)
  0ngrp $p |- -. (/) e. GrpOp $=
    ( c0 cgr wcel wne neirr crn rn0 eqcomi grpon0 mto ) ABCAADAEAAAFAGHIJ $.

  ${
    $d g u x G $.  $d g u x X $.
    gidval.1 $e |- X = ran G $.
    $( The value of the identity element of a group.  (Contributed by Mario
       Carneiro, 15-Dec-2013.)  (New usage is discouraged.) $)
    gidval $p |- ( G e. V -> ( GId ` G ) =
             ( iota_ u e. X A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) ) ) $=
      ( vg wcel cvv cgi cfv cv co wceq wa wral crio crn oveq eqeq1d riotaeqbidv
      elex rneq eqtr4di anbi12d raleqbidv df-gid riotaex fvmpt syl ) CDHCIHCJKB
      LZALZCMZULNZULUKCMZULNZOZAEPZBEQZNCDUBGCUKULGLZMZULNZULUKUTMZULNZOZAUTRZP
      ZBVFQUSIJUTCNZVGURBVFEVHVFCREUTCUCFUDZVHVEUQAVFEVIVHVBUNVDUPVHVAUMULUKULU
      TCSTVHVCUOULULUKUTCSTUEUFUAABGUGURBEUHUIUJ $.
  $}

  ${
    $d x y A $.  $d u x y G $.  $d u x y U $.  $d u x y X $.
    grpoidval.1 $e |- X = ran G $.
    grpoidval.2 $e |- U = ( GId ` G ) $.
    $( Lemma for ~ grpoidcl and others.  (Contributed by NM, 5-Feb-2010.)
       (Proof shortened by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoidval $p |- ( G e. GrpOp -> U =
                     ( iota_ u e. X A. x e. X ( u G x ) = x ) ) $=
      ( vy cgr wcel cgi cv co wceq wral crio wa wrex simpl ralimi cfv gidval wi
      wreu w3a rgenw a1i grpoidinv reximi syl grpoideu 3jca reupick2 riotabidva
      wb sylan eqtr4d eqtrid ) DIJZCDKUAZBLZALZDMVBNZAEOZBEPZGUSUTVCVBVADMVBNZQ
      ZAEOZBEPVEABDIEFUBUSVDVHBEUSVHVDUCZBEOZVHBERZVDBEUDZUEVAEJVDVHUOUSVJVKVLV
      JUSVIBEVGVCAEVCVFSTUFUGUSVGHLZVBDMVANVBVMDMVANQHERZQZAEOZBERVKAHBDEFUHVPV
      HBEVOVGAEVGVNSTUIUJABDEFUKULVDVHBEUMUPUNUQUR $.

    $( The identity element of a group belongs to the group.  (Contributed by
       NM, 24-Oct-2006.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoidcl $p |- ( G e. GrpOp -> U e. X ) $=
      ( vu vx cgr wcel cv co wceq wral crio grpoidval wreu grpoideu riotacl syl
      eqeltrd ) BHIZAFJGJZBKUBLGCMZFCNZCGFABCDEOUAUCFCPUDCIGFBCDQUCFCRST $.

    $( A group's properties using the explicit identity element.  (Contributed
       by NM, 5-Feb-2010.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoidinv2 $p |- ( ( G e. GrpOp /\ A e. X ) -> ( ( ( U G A ) = A /\
         ( A G U ) = A ) /\ E. y e. X ( ( y G A ) = U /\ ( A G y ) = U ) ) ) $=
      ( vx vu wcel cv co wceq wa wrex wral oveq1 eqeq1d oveq2 anbi12d crab crio
      cgr grpoidval grpoideu riotacl2 syl eqeltrd wi w3a wb simpll ralimi rgenw
      wreu grpoidinv 3jca reupick2 sylan rabbidva eleqtrd eqeq2 rexbidv ralbidv
      a1i elrab sylib simprd id eqeq12d rspccva ) DUCJZCHKZDLZVMMZVMCDLZVMMZNZA
      KZVMDLZCMZVMVSDLZCMZNZAEOZNZHEPZBEJCBDLZBMZBCDLZBMZNZVSBDLZCMZBVSDLZCMZNZ
      AEOZNZVLCEJZWGVLCIKZVMDLZVMMZVMXADLZVMMZNZVTXAMZWBXAMZNZAEOZNZHEPZIEUAZJW
      TWGNVLCXCHEPZIEUAZXMVLCXNIEUBZXOHICDEFGUDVLXNIEUOZXPXOJHIDEFUEZXNIEUFUGUH
      VLXNXLIEVLXLXNUIZIEPZXLIEOZXQUJXAEJXNXLUKVLXTYAXQXTVLXSIEXKXCHEXCXEXJULUM
      UNVEHAIDEFUPXRUQXNXLIEURUSUTVAXLWGICEXACMZXKWFHEYBXFVRXJWEYBXCVOXEVQYBXBV
      NVMXACVMDQRYBXDVPVMXACVMDSRTYBXIWDAEYBXGWAXHWCXACVTVBXACWBVBTVCTVDVFVGVHW
      FWSHBEVMBMZVRWLWEWRYCVOWIVQWKYCVNWHVMBVMBCDSYCVIZVJYCVPWJVMBVMBCDQYDVJTYC
      WDWQAEYCWAWNWCWPYCVTWMCVMBVSDSRYCWBWOCVMBVSDQRTVCTVKUS $.

    $( The identity element of a group is a left identity.  (Contributed by NM,
       24-Oct-2006.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpolid $p |- ( ( G e. GrpOp /\ A e. X ) -> ( U G A ) = A ) $=
      ( vy cgr wcel wa co wceq cv wrex grpoidinv2 simplld ) CHIADIJBACKALABCKAL
      GMZACKBLAQCKBLJGDNGABCDEFOP $.

    $( The identity element of a group is a right identity.  (Contributed by
       NM, 24-Oct-2006.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grporid $p |- ( ( G e. GrpOp /\ A e. X ) -> ( A G U ) = A ) $=
      ( vx cgr wcel wa co wceq cv wrex grpoidinv2 simplr syl ) CHIADIJBACKALZAB
      CKALZJGMZACKBLATCKBLJGDNZJSGABCDEFORSUAPQ $.
  $}

  ${
    $d y A $.  $d y B $.  $d y C $.  $d y G $.  $d y X $.
    grprcan.1 $e |- X = ran G $.
    $( Right cancellation law for groups.  (Contributed by NM, 26-Oct-2006.)
       (New usage is discouraged.) $)
    grporcan $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                  ( ( A G C ) = ( B G C ) <-> A = B ) ) $=
      ( vy wcel co wceq wrex adantl oveq1 grpoass adantrr 3eqtr3d oveq2 grporid
      wa ad2antrl cgr wb cv cgi cfv wi eqid grpoidinv2 simpr ad2ant2rl ad2antll
      reximi 3anassrs adantlrl 3exp2 adantllr adantrrl ad2antrr ad2ant2r adantr
      syl imp42 exp45 rexlimdv mpd impbid1 exp43 3imp2 ) DUAHZAEHZBEHZCEHZACDIZ
      BCDIZJZABJZUBZVIVJVKVLVQVIVJSZVKVLSZSZVOVPVTCGUCZDIZDUDUEZJZGEKZVOVPUFZVI
      VLWEVJVKVIVLSWCCDICJCWCDICJSZWACDIWCJZWDSZGEKZSWEGCWCDEFWCUGZUHWJWEWGWIWD
      GEWHWDUIULLVAUJVTWDWFGEVTWAEHZWDVOVPVTWLWDVOSSZSZAWCDIZBWCDIZABWNAWBDIZBW
      BDIZWOWPVTWLVOWQWRJWDVTWLVOSSVMWADIZVNWADIZWQWRVOWSWTJVTWLVMVNWADMUKVTWLW
      SWQJZVOVRVLWLXAVKVIVJVLWLXAACWADEFNUMUNOVTWLWTWRJZVOVIVSWLXBVJVIVKVLWLXBV
      IVKVLWLXBBCWADEFNUOVBUPOPUQWMWQWOJZVTWDXCWLVOWBWCADQTLWMWRWPJZVTWDXDWLVOW
      BWCBDQTLPVRWOAJVSWMAWCDEFWKRURVTWPBJZWMVIVKXEVJVLBWCDEFWKRUSUTPVCVDVEABCD
      MVFVGVH $.
  $}

  ${
    $d y z A $.  $d y z G $.  $d y z U $.  $d y z X $.
    grpoinveu.1 $e |- X = ran G $.
    grpoinveu.2 $e |- U = ( GId ` G ) $.
    $( The left inverse element of a group is unique.  Lemma 2.2.1(b) of
       [Herstein] p. 55.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpoinveu $p |- ( ( G e. GrpOp /\ A e. X ) -> E! y e. X ( y G A ) = U ) $=
      ( vz cgr wcel wa cv co wceq wi wral wrex wreu grpoidinv2 simpl reximi syl
      adantl w3a eqtr3 grporcan imbitrid 3exp2 com24 imp41 an32s expd ralrimdva
      ancld reximdva mpd oveq1 eqeq1d reu8 sylibr ) DIJZBEJZKZALZBDMZCNZHLZBDMZ
      CNZVDVGNZOZHEPZKZAEQZVFAERVCVFAEQZVNVCCBDMBNBCDMBNKZVFBVDDMCNZKZAEQZKVOAB
      CDEFGSVSVOVPVRVFAEVFVQTUAUCUBVCVFVMAEVCVDEJZKZVFVLWAVFVKHEWAVGEJZKVFVIVJV
      CWBVTVFVIKZVJOZVAVBWBVTWDVAVTWBVBWDVAVTWBVBWDWCVEVHNVAVTWBVBUDKVJVEVHCUEV
      DVGBDEFUFUGUHUIUJUKULUMUNUOUPVFVIAHEVJVEVHCVDVGBDUQURUSUT $.

    $( Two ways of saying that an element of a group is the identity element.
       (Contributed by Paul Chapman, 25-Feb-2008.)
       (New usage is discouraged.) $)
    grpoid $p |- ( ( G e. GrpOp /\ A e. X ) ->
                  ( A = U <-> ( A G A ) = A ) ) $=
      ( cgr wcel wa co wceq wb grpoidcl grporcan 3exp2 mpid pm2.43d imp grpolid
      wi eqeq2d bitr3d ) CGHZADHZIZAACJZBACJZKZABKZUFAKUCUDUHUILZUCUDUJUCUDBDHZ
      UDUJTBCDEFMUCUDUKUDUJABACDENOPQRUEUGAUFABCDEFSUAUB $.
  $}

  ${
    grprn.1 $e |- G e. GrpOp $.
    grprn.2 $e |- dom G = ( X X. X ) $.
    $( The range of a group operation.  Useful for satisfying group base set
       hypotheses of the form ` X = ran G ` .  (Contributed by NM, 5-Nov-2006.)
       (New usage is discouraged.) $)
    grporn $p |- X = ran G $=
      ( cxp wfn crn wceq wfun cdm cgr wcel wfo eqid grpofo fofun df-fn mpbir2an
      mp2b fofn wa fndmu xpid11 sylib mp2an ) ABBEZFZAAGZUHEZFZBUHHZUGAIZAJUFHA
      KLZUIUHAMZULCAUHUHNOZUIUHAPSDAUFQRUMUNUJCUOUIUHATSUGUJUAUFUIHUKUFUIAUBBUH
      UCUDUE $.
  $}

  ${
    $d x y A $.  $d g x y G $.  $d g x y X $.  $d g x U $.
    grpinvfval.1 $e |- X = ran G $.
    grpinvfval.2 $e |- U = ( GId ` G ) $.
    grpinvfval.3 $e |- N = ( inv ` G ) $.
    $( The inverse function of a group.  (Contributed by NM, 26-Oct-2006.)
       (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoinvfval $p |- ( G e. GrpOp -> N = ( x e. X |->
                     ( iota_ y e. X ( y G x ) = U ) ) ) $=
      ( vg cgr wcel cgn cfv cv co wceq crio cvv cgi cmpt crn rnexg eqeltrid syl
      mptexg rneq eqtr4di oveq fveq2 eqeq12d riotaeqbidv mpteq12dv fvmptg mpdan
      df-ginv eqtrid ) DKLZEDMNZAFBOZAOZDPZCQZBFRZUAZIURVESLZUSVEQURFSLVFURFDUB
      ZSGDKUCUDAFVDSUFUEJDAJOZUBZUTVAVHPZVHTNZQZBVIRZUAVEKSMVHDQZAVIVMFVDVNVIVG
      FVHDUGGUHZVNVLVCBVIFVOVNVJVBVKCUTVAVHDUIVNVKDTNCVHDTUJHUHUKULUMABJUPUNUOU
      Q $.

    $( The inverse of a group element.  (Contributed by NM, 26-Oct-2006.)
       (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoinvval $p |- ( ( G e. GrpOp /\ A e. X ) ->
                    ( N ` A ) = ( iota_ y e. X ( y G A ) = U ) ) $=
      ( vx cgr wcel cfv cv co wceq crio cmpt grpoinvfval fveq1d oveq2 riotabidv
      eqeq1d eqid riotaex fvmpt sylan9eq ) DKLZBFLBEMBJFANZJNZDOZCPZAFQZRZMUIBD
      OZCPZAFQZUHBEUNJACDEFGHISTJBUMUQFUNUJBPZULUPAFURUKUOCUJBUIDUAUCUBUNUDUPAF
      UEUFUG $.
  $}

  ${
    $d y A $.  $d y G $.  $d y X $.
    grpinvcl.1 $e |- X = ran G $.
    grpinvcl.2 $e |- N = ( inv ` G ) $.
    $( A group element's inverse is a group element.  (Contributed by NM,
       27-Oct-2006.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoinvcl $p |- ( ( G e. GrpOp /\ A e. X ) -> ( N ` A ) e. X ) $=
      ( vy cgr wcel wa cfv cv co cgi wceq crio eqid grpoinvval wreu grpoinveu
      riotacl syl eqeltrd ) BHIADIJZACKGLABMBNKZOZGDPZDGAUEBCDEUEQZFRUDUFGDSUGD
      IGAUEBDEUHTUFGDUAUBUC $.
  $}

  ${
    $d y A $.  $d y G $.  $d y N $.  $d y U $.  $d y X $.
    grpinv.1 $e |- X = ran G $.
    grpinv.2 $e |- U = ( GId ` G ) $.
    grpinv.3 $e |- N = ( inv ` G ) $.
    $( The properties of a group element's inverse.  (Contributed by NM,
       27-Oct-2006.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoinv $p |- ( ( G e. GrpOp /\ A e. X ) ->
                 ( ( ( N ` A ) G A ) = U /\ ( A G ( N ` A ) ) = U ) ) $=
      ( vy cgr wcel wa cfv co wceq cv crab crio simprd eqeq1d wreu riotacl2 syl
      grpoinvval grpoinveu eqeltrd wi wral wrex w3a simpl rgenw grpoidinv2 3jca
      wb a1i reupick2 sylan rabbidva eleqtrd oveq1 oveq2 anbi12d elrab sylib )
      CJKAEKLZADMZEKZVGACNZBOZAVGCNZBOZLZVFVGIPZACNZBOZAVNCNZBOZLZIEQZKVHVMLVFV
      GVPIEQZVTVFVGVPIERZWAIABCDEFGHUDVFVPIEUAZWBWAKIABCEFGUEZVPIEUBUCUFVFVPVSI
      EVFVSVPUGZIEUHZVSIEUIZWCUJVNEKVPVSUOVFWFWGWCWFVFWEIEVPVRUKULUPVFBACNAOABC
      NAOLWGIABCEFGUMSWDUNVPVSIEUQURUSUTVSVMIVGEVNVGOZVPVJVRVLWHVOVIBVNVGACVATW
      HVQVKBVNVGACVBTVCVDVES $.

    $( The left inverse of a group element.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpolinv $p |- ( ( G e. GrpOp /\ A e. X ) -> ( ( N ` A ) G A ) = U ) $=
      ( cgr wcel wa cfv co wceq grpoinv simpld ) CIJAEJKADLZACMBNAQCMBNABCDEFGH
      OP $.

    $( The right inverse of a group element.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grporinv $p |- ( ( G e. GrpOp /\ A e. X ) -> ( A G ( N ` A ) ) = U ) $=
      ( cgr wcel wa cfv co wceq grpoinv simprd ) CIJAEJKADLZACMBNAQCMBNABCDEFGH
      OP $.

    $( The inverse of a group element expressed in terms of the identity
       element.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpoinvid1 $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                    ( ( N ` A ) = B <-> ( A G B ) = U ) ) $=
      ( wcel w3a wceq co wa oveq2 adantl 3adant3 adantr eqtr3d syldan grpoinvcl
      cgr cfv grporinv grpolinv oveq1d adantrr simprl simprr 3jca grpoass 3impb
      grpolid 3adant2 grporid 3eqtr3rd impbida ) DUBJZAFJZBFJZKZAEUCZBLZABDMZCL
      ZVAVCNAVBDMZVDCVCVFVDLVAVBBADOPVAVFCLZVCURUSVGUTACDEFGHIUDQRSVAVENVBVDDMZ
      VBCDMZBVBVEVHVILVAVDCVBDOPVAVHBLVEVACBDMZVHBVAVBADMZBDMZVJVHURUSVLVJLUTUR
      USNVKCBDACDEFGHIUEUFQURUSUTVLVHLZURUSUTNZVBFJZUSUTKVMURVNNVOUSUTURUSVOUTA
      DEFGIUAZUGURUSUTUHURUSUTUIUJVBABDFGUKTULSURUTVJBLUSBCDFGHUMUNSRVAVIVBLZVE
      URUSVQUTURUSVOVQVPVBCDFGHUOTQRUPUQ $.

    $( The inverse of a group element expressed in terms of the identity
       element.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpoinvid2 $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                    ( ( N ` A ) = B <-> ( B G A ) = U ) ) $=
      ( cgr wcel w3a wceq co wa oveq1 adantl 3adant3 adantr syldan cfv grpolinv
      eqtr3d grpoinvcl grpolid eqcomd simprr simprl adantrr 3jca 3impb grporinv
      grpoass oveq2d grporid 3adant2 3eqtrd 3eqtr2d impbida ) DJKZAFKZBFKZLZAEU
      AZBMZBADNZCMZVCVEOVDADNZVFCVEVHVFMVCVDBADPQVCVHCMZVEUTVAVIVBACDEFGHIUBRSU
      CVCVGOVDCVDDNZVFVDDNZBVCVDVJMVGVCVJVDUTVAVJVDMZVBUTVAVDFKZVLADEFGIUDZVDCD
      FGHUETRUFSVGVKVJMVCVFCVDDPQVCVKBMVGVCVKBAVDDNZDNZBCDNZBUTVAVBVKVPMZUTVAVB
      OZVBVAVMLVRUTVSOVBVAVMUTVAVBUGUTVAVBUHUTVAVMVBVNUIUJBAVDDFGUMTUKUTVAVPVQM
      VBUTVAOVOCBDACDEFGHIULUNRUTVBVQBMVABCDFGHUOUPUQSURUS $.
  $}

  ${
    grplcan.1 $e |- X = ran G $.
    $( Left cancellation law for groups.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpolcan $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                  ( ( C G A ) = ( C G B ) <-> A = B ) ) $=
      ( wcel w3a wa co wceq cfv oveq2 eqid adantlr oveq1d adantrl simprr adantr
      3eqtr3d cgr cgn adantl cgi grpolinv grpoinvcl simprl 3jca grpoass anassrs
      wi syldan grpolid adantrr exp53 3imp2 impbid1 ) DUAGZAEGZBEGZCEGZHICADJZC
      BDJZKZABKZURUSUTVAVDVEUKURUSUTVAVDVEURUSIZUTVAIZIZVDICDUBLZLZVBDJZVJVCDJZ
      ABVDVKVLKVHVBVCVJDMUCVHVKAKZVDVFVAVMUTVFVAIZVJCDJZADJZDUDLZADJZVKAVNVOVQA
      DURVAVOVQKZUSCVQDVIEFVQNZVINZUEZOPURUSVAVPVKKZURUSVAIZVJEGZVAUSHWCURWDIWE
      VAUSURVAWEUSCDVIEFWAUFZQURUSVARURUSVAUGUHVJCADEFUIULUJVFVRAKVAAVQDEFVTUMS
      TQSVHVLBKZVDURVGWGUSURVGIZVOBDJZVQBDJZVLBWHVOVQBDURVAVSUTWBQPURVGWEVAUTHW
      IVLKWHWEVAUTURVAWEUTWFQURUTVARURUTVAUGUHVJCBDEFUIULURUTWJBKVABVQDEFVTUMUN
      TOSTUOUPABCDMUQ $.
  $}

  ${
    $d x y G $.  $d x y N $.  $d x y X $.
    grpasscan1.1 $e |- X = ran G $.
    grpasscan1.2 $e |- N = ( inv ` G ) $.
    $( Double inverse law for groups.  Lemma 2.2.1(c) of [Herstein] p. 55.
       (Contributed by NM, 27-Oct-2006.)  (New usage is discouraged.) $)
    grpo2inv $p |- ( ( G e. GrpOp /\ A e. X ) -> ( N ` ( N ` A ) ) = A ) $=
      ( cgr wcel wa cfv wceq cgi grpoinvcl eqid grporinv syldan grpolinv eqtr4d
      co w3a wb simpr 3jca grpolcan mpbid ) BGHZADHZIZACJZUICJZBSZUIABSZKZUJAKZ
      UHUKBLJZULUFUGUIDHZUKUOKABCDEFMZUIUOBCDEUONZFOPAUOBCDEURFQRUFUGUJDHZUGUPT
      UMUNUAUHUSUGUPUFUGUPUSUQUIBCDEFMPUFUGUBUQUCUJAUIBDEUDPUE $.

    $( Mapping of the inverse function of a group.  (Contributed by NM,
       29-Mar-2008.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpoinvf $p |- ( G e. GrpOp -> N : X -1-1-onto-> X ) $=
      ( vx vy cgr wcel wfn crn wceq cv cfv wral eqid grpoinvcl grpo2inv fveq2
      wa wi wf1o co cgi crio cmpt riotaex fnmpti grpoinvfval fneq1d mpbiri wrex
      cab fnrnfv syl eqcomd rspceeqv syl2anc ex simpr adantr eqeltrd rexlimdva2
      impbid eqabdv eqtr4d wb eqeqan12d anandis imbitrid ralrimivva syl3anbrc
      dff1o6 ) AHIZBCJZBKZCLFMZBNZGMZBNZLZVQVSLZUAZGCOFCOCCBUBVNVOFCVSVQAUCAUDN
      ZLZGCUEZUFZCJFCWFWGWEGCUGWGPUHVNCBWGFGWDABCDWDPEUIUJUKZVNVPVSVRLZFCULZGUM
      ZCVNVOVPWKLWHFGCBUNUOVNWJGCVNVSCIZWJVNWLWJVNWLTZVTCIVSVTBNZLWJVSABCDEQWMW
      NVSVSABCDERZUPFVTCVRWNVSVQVTBSUQURUSVNWIWLFCVNVQCIZTZWITVSVRCWQWIUTWQVRCI
      WIVQABCDEQVAVBVCVDVEVFVNWCFGCCWAVRBNZWNLZVNWPWLTTWBVRVTBSVNWPWLWSWBVGWQWM
      WRVQWNVSVQABCDERWOVHVIVJVKFGCCBVMVL $.

    $( The inverse of the group operation reverses the arguments.  Lemma
       2.2.1(d) of [Herstein] p. 55.  (Contributed by NM, 27-Oct-2006.)
       (New usage is discouraged.) $)
    grpoinvop $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                   ( N ` ( A G B ) ) = ( ( N ` B ) G ( N ` A ) ) ) $=
      ( cgr wcel co cfv wceq grpoinvcl 3adant2 3adant3 syl3anc grpoass syl13anc
      grpocl grporinv w3a simp1 simp2 eqid oveq1d grpolid syldan 3eqtr3d oveq2d
      cgi simp3 3eqtrd wb grpoinvid1 mpbird ) CHIZAEIZBEIZUAZABCJZDKBDKZADKZCJZ
      LZUTVCCJZCUJKZLZUSVEABVCCJZCJZAVBCJZVFUSUPUQURVCEIZVEVILUPUQURUBZUPUQURUC
      UPUQURUKZUSUPVAEIZVBEIZVKVLUPURVNUQBCDEFGMNZUPUQVOURACDEFGMZOZVAVBCEFSPZA
      BVCCEFQRUSVHVBACUSBVACJZVBCJZVFVBCJZVHVBUSVTVFVBCUPURVTVFLUQBVFCDEFVFUDZG
      TNUEUSUPURVNVOWAVHLVLVMVPVRBVAVBCEFQRUPUQWBVBLZURUPUQVOWDVQVBVFCEFWCUFUGO
      UHUIUPUQVJVFLURAVFCDEFWCGTOULUSUPUTEIVKVDVGUMVLABCEFSVSUTVCVFCDEFWCGUNPUO
      $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d g x y G $.  $d g x y N $.  $d g x y X $.
    grpdiv.1 $e |- X = ran G $.
    grpdiv.2 $e |- N = ( inv ` G ) $.
    grpdiv.3 $e |- D = ( /g ` G ) $.
    $( Group division (or subtraction) operation.  (Contributed by NM,
       15-Feb-2008.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpodivfval $p |- ( G e. GrpOp -> D = ( x e. X , y e. X |->
                       ( x G ( N ` y ) ) ) ) $=
      ( vg cgr wcel cgs cfv cv co cmpo cvv wceq cgn rnexg eqeltrid mpoexga rneq
      crn syl2anc eqtr4di eqidd fveq2 fveq1d oveq123d mpoeq123dv df-gdiv fvmptg
      id mpdan eqtrid ) DKLZCDMNZABFFAOZBOZENZDPZQZIURVDRLZUSVDSURFRLZVFVEURFDU
      EZRGDKUAUBZVHABFFVCRRUCUFJDABJOZUEZVJUTVAVITNZNZVIPZQVDKRMVIDSZABVJVJVMFF
      VCVNVJVGFVIDUDGUGZVOVNUTUTVLVBVIDVNUOVNUTUHVNVAVKEVNVKDTNEVIDTUIHUGUJUKUL
      ABJUMUNUPUQ $.

    $( Group division (or subtraction) operation value.  (Contributed by NM,
       15-Feb-2008.)  (Revised by Mario Carneiro, 15-Dec-2013.)
       (New usage is discouraged.) $)
    grpodivval $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                   ( A D B ) = ( A G ( N ` B ) ) ) $=
      ( vx vy cgr wcel co cfv wceq wa cv cmpo grpodivfval oveqd oveq1 eqid ovex
      fveq2 oveq2d ovmpo sylan9eq 3impb ) DLMZAFMZBFMZABCNZABEOZDNZPUJUKULQUMAB
      JKFFJRZKRZEOZDNZSZNUOUJCUTABJKCDEFGHITUAJKABFFUSUOUTAURDNUPAURDUBUQBPURUN
      ADUQBEUEUFUTUCAUNDUDUGUHUI $.

    $( Group division by an inverse.  (Contributed by NM, 15-Feb-2008.)
       (New usage is discouraged.) $)
    grpodivinv $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                   ( A D ( N ` B ) ) = ( A G B ) ) $=
      ( cgr wcel w3a cfv co wceq grpoinvcl 3adant2 grpodivval syld3an3 grpo2inv
      oveq2d eqtrd ) DJKZAFKZBFKZLZABEMZCNZAUGEMZDNZABDNUCUDUEUGFKZUHUJOUCUEUKU
      DBDEFGHPQAUGCDEFGHIRSUFUIBADUCUEUIBOUDBDEFGHTQUAUB $.

    $( Inverse of a group division.  (Contributed by NM, 24-Feb-2008.)
       (New usage is discouraged.) $)
    grpoinvdiv $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                   ( N ` ( A D B ) ) = ( B D A ) ) $=
      ( cgr wcel w3a co cfv grpodivval fveq2d wceq grpoinvcl 3adant2 grpoinvop
      syld3an3 grpo2inv oveq1d 3com23 eqtr4d 3eqtrd ) DJKZAFKZBFKZLZABCMZENABEN
      ZDMZENZULENZAENZDMZBACMZUJUKUMEABCDEFGHIOPUGUHUIULFKZUNUQQUGUIUSUHBDEFGHR
      SAULDEFGHTUAUJUQBUPDMZURUJUOBUPDUGUIUOBQUHBDEFGHUBSUCUGUIUHURUTQBACDEFGHI
      OUDUEUF $.
  $}

  ${
    $d x y G $.  $d x y X $.
    grpdivf.1 $e |- X = ran G $.
    grpdivf.3 $e |- D = ( /g ` G ) $.
    $( Mapping for group division.  (Contributed by NM, 10-Apr-2008.)  (Revised
       by Mario Carneiro, 15-Dec-2013.)  (New usage is discouraged.) $)
    grpodivf $p |- ( G e. GrpOp -> D : ( X X. X ) --> X ) $=
      ( vx vy cgr wcel cxp wf cv cgn cfv co cmpo wral eqid grpoinvcl 3adant2
      grpocl syld3an3 3expib ralrimivv fmpo sylib grpodivfval feq1d mpbird ) BH
      IZCCJZCAKUKCFGCCFLZGLZBMNZNZBOZPZKZUJUPCIZGCQFCQURUJUSFGCCUJULCIZUMCIZUSU
      JUTVAUOCIZUSUJVAVBUTUMBUNCDUNRZSTULUOBCDUAUBUCUDFGCCUPCUQUQRUEUFUJUKCAUQF
      GABUNCDVCEUGUHUI $.

    $( Closure of group division (or subtraction) operation.  (Contributed by
       NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    grpodivcl $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( A D B ) e. X ) $=
      ( cgr wcel cxp wf co grpodivf fovcdm syl3an1 ) DHIEEJECKAEIBEIABCLEICDEFG
      MABEEECNO $.

    $( Double group division.  (Contributed by NM, 24-Feb-2008.)
       (New usage is discouraged.) $)
    grpodivdiv $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
         ( A D ( B D C ) ) = ( A G ( C D B ) ) ) $=
      ( cgr wcel w3a wa co cgn cfv wceq simpl simpr1 grpodivcl 3adant3r1 oveq2d
      eqid grpodivval syl3anc grpoinvdiv eqtrd ) EIJZAFJZBFJZCFJZKZLZABCDMZDMZA
      UMENOZOZEMZACBDMZEMULUGUHUMFJZUNUQPUGUKQUGUHUIUJRUGUIUJUSUHBCDEFGHSTAUMDE
      UOFGUOUBZHUCUDULUPURAEUGUIUJUPURPUHBCDEUOFGUTHUETUAUF $.

    $( Associative-type law for multiplication and division.  (Contributed by
       NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    grpomuldivass $p |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
         ( ( A G B ) D C ) = ( A G ( B D C ) ) ) $=
      ( cgr wcel w3a wa co cgn cfv wceq simpr1 simpr2 eqid grpodivval grpoinvcl
      3ad2antr3 grpoass syldan grpocl 3adant3r3 simpr3 syl3anc 3adant3r1 oveq2d
      3jca simpl 3eqtr4d ) EIJZAFJZBFJZCFJZKZLZABEMZCENOZOZEMZABVBEMZEMZUTCDMZA
      BCDMZEMUNURUOUPVBFJZKVCVEPUSUOUPVHUNUOUPUQQUNUOUPUQRUNUOUQVHUPCEVAFGVASZU
      AUBUKABVBEFGUCUDUSUNUTFJZUQVFVCPUNURULUNUOUPVJUQABEFGUEUFUNUOUPUQUGUTCDEV
      AFGVIHTUHUSVGVDAEUNUPUQVGVDPUOBCDEVAFGVIHTUIUJUM $.

    ${
      grpdivid.3 $e |- U = ( GId ` G ) $.
      $( Division of a group member by itself.  (Contributed by NM,
         15-Feb-2008.)  (New usage is discouraged.) $)
      grpodivid $p |- ( ( G e. GrpOp /\ A e. X ) -> ( A D A ) = U ) $=
        ( cgr wcel wa co cgn cfv wceq eqid grpodivval 3anidm23 grporinv eqtrd )
        DIJZAEJZKAABLZAADMNZNDLZCUAUBUCUEOAABDUDEFUDPZGQRACDUDEFHUFST $.
    $}

    $( Cancellation law for group division.  ( ~ npcan analog.)  (Contributed
       by NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    grponpcan $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
        ( ( A D B ) G B ) = A ) $=
      ( cgr wcel w3a co cgn cfv eqid grpodivval oveq1d wceq simp1 3adant2 eqtrd
      simp2 grpoinvcl simp3 grpoass syl13anc wa grpolinv oveq2d grporid 3adant3
      cgi ) DHIZAEIZBEIZJZABCKZBDKABDLMZMZDKZBDKZAUOUPUSBDABCDUQEFUQNZGOPUOUTAU
      RBDKZDKZAUOULUMUREIZUNUTVCQULUMUNRULUMUNUAULUNVDUMBDUQEFVAUBSULUMUNUCAURB
      DEFUDUEUOVCADUKMZDKZAULUNVCVFQUMULUNUFVBVEADBVEDUQEFVENZVAUGUHSULUMVFAQUN
      AVEDEFVGUIUJTTT $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Abelian groups
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c AbelOp $.

  $( Extend class notation with the class of all Abelian group operations. $)
  cablo $a class AbelOp $.

  ${
    $d g x y $.
    $( Define the class of all Abelian group operations.  (Contributed by NM,
       2-Nov-2006.)  (New usage is discouraged.) $)
    df-ablo $a |- AbelOp
     = { g e. GrpOp | A. x e. ran g A. y e. ran g ( x g y ) = ( y g x ) } $.
  $}

  ${
    $d g x y G $.  $d g x y X $.
    isabl.1 $e |- X = ran G $.
    $( The predicate "is an Abelian (commutative) group operation."
       (Contributed by NM, 2-Nov-2006.)  (New usage is discouraged.) $)
    isablo $p |- ( G e. AbelOp <-> ( G e. GrpOp /\
             A. x e. X A. y e. X ( x G y ) = ( y G x ) ) ) $=
      ( vg cv co wceq crn wral cgr cablo rneq eqtr4di raleq raleqbi1dv syl oveq
      wb eqeq12d 2ralbidv bitrd df-ablo elrab2 ) AGZBGZFGZHZUGUFUHHZIZBUHJZKZAU
      LKZUFUGCHZUGUFCHZIZBDKADKZFCLMUHCIZUNUKBDKZADKZURUSULDIUNVATUSULCJDUHCNEO
      UMUTAULDUKBULDPQRUSUKUQABDDUSUIUOUJUPUFUGUHCSUGUFUHCSUAUBUCABFUDUE $.
  $}

  ${
    $d x y G $.
    $( An Abelian group operation is a group operation.  (Contributed by NM,
       2-Nov-2006.)  (New usage is discouraged.) $)
    ablogrpo $p |- ( G e. AbelOp -> G e. GrpOp ) $=
      ( vx vy cablo wcel cgr cv co wceq crn wral eqid isablo simplbi ) ADEAFEBG
      ZCGZAHPOAHICAJZKBQKBCAQQLMN $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y G $.  $d x y X $.
    ablcom.1 $e |- X = ran G $.
    $( An Abelian group operation is commutative.  (Contributed by NM,
       2-Nov-2006.)  (New usage is discouraged.) $)
    ablocom $p |- ( ( G e. AbelOp /\ A e. X /\ B e. X ) ->
                 ( A G B ) = ( B G A ) ) $=
      ( vx vy cablo wcel co wceq cv wral cgr isablo simprbi oveq1 oveq2 eqeq12d
      wa rspc2v syl5com 3impib ) CHIZADIZBDIZABCJZBACJZKZUDFLZGLZCJZUKUJCJZKZGD
      MFDMZUEUFTUIUDCNIUOFGCDEOPUNUIAUKCJZUKACJZKFGABDDUJAKULUPUMUQUJAUKCQUJAUK
      CRSUKBKUPUGUQUHUKBACRUKBACQSUAUBUC $.

    $( Commutative/associative law for Abelian groups.  (Contributed by NM,
       26-Apr-2007.)  (New usage is discouraged.) $)
    ablo32 $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( ( A G B ) G C ) = ( ( A G C ) G B ) ) $=
      ( cablo wcel w3a wa co wceq ablocom 3adant3r1 oveq2d cgr ablogrpo grpoass
      sylan 3ancomb sylan2b 3eqtr4d ) DGHZAEHZBEHZCEHZIZJZABCDKZDKZACBDKZDKZABD
      KCDKZACDKBDKZUHUIUKADUCUEUFUIUKLUDBCDEFMNOUCDPHZUGUMUJLDQZABCDEFRSUCUOUGU
      NULLZUPUGUOUDUFUEIUQUDUEUFTACBDEFRUASUB $.

    $( Commutative/associative law for Abelian groups.  (Contributed by NM,
       26-Apr-2007.)  (New usage is discouraged.) $)
    ablo4 $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X ) /\ ( C e. X /\
   D e. X ) ) -> ( ( A G B ) G ( C G D ) ) = ( ( A G C ) G ( B G D ) ) ) $=
      ( wcel wa wceq w3a simprlr simprrl 3jca syldan grpocl 3expb grpoass sylan
      co cablo simprll ablo32 oveq1d ablogrpo adantrr simprrr adantrlr adantrrr
      cgr 3eqtr3d 3impb ) EUAHZAFHZBFHZIZCFHZDFHZIZABETZCDETETZACETZBDETETZJUMU
      PUSIZIZUTCETZDETZVBBETZDETZVAVCVEVFVHDEUMVDUNUOUQKVFVHJVEUNUOUQUMUNUOUSUB
      UMUNUOUSLUMUPUQURMNABCEFGUCOUDUMEUJHZVDVGVAJZEUEZVJVDUTFHZUQURKVKVJVDIZVM
      UQURVJUPVMUSVJUNUOVMABEFGPQUFVJUPUQURMVJUPUQURUGZNUTCDEFGROSUMVJVDVIVCJZV
      LVJVDVBFHZUOURKVPVNVQUOURVJUPUQVQURVJUNUQVQUOVJUNUQVQACEFGPQUHUIVJUNUOUSL
      VONVBBDEFGROSUKUL $.
  $}

  ${
    $d x y G $.  $d x y X $.
    isabli.1 $e |- G e. GrpOp $.
    isabli.2 $e |- dom G = ( X X. X ) $.
    isabli.3 $e |- ( ( x e. X /\ y e. X ) -> ( x G y ) = ( y G x ) ) $.
    $( Properties that determine an Abelian group operation.  (Contributed by
       NM, 5-Nov-2006.)  (New usage is discouraged.) $)
    isabloi $p |- G e. AbelOp $=
      ( cablo wcel cgr cv co wceq wral rgen2 grporn isablo mpbir2an ) CHICJIAKZ
      BKZCLTSCLMZBDNADNEUAABDDGOABCDCDEFPQR $.
  $}

  ${
    abldiv.1 $e |- X = ran G $.
    abldiv.3 $e |- D = ( /g ` G ) $.
    $( Law for group multiplication and division.  (Contributed by NM,
       15-Feb-2008.)  (New usage is discouraged.) $)
    ablomuldiv $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
     ( ( A G B ) D C ) = ( ( A D C ) G B ) ) $=
      ( cablo wcel w3a wa co wceq ablocom 3adant3r3 oveq1d 3ancoma cgr ablogrpo
      grpomuldivass sylan sylan2b simpr2 grpodivcl syl3an1 3adant3r2 jca syldan
      3expb 3eqtrd ) EIJZAFJZBFJZCFJZKZLZABEMZCDMBAEMZCDMZBACDMZEMZVABEMZUQURUS
      CDULUMUNURUSNUOABEFGOPQUPULUNUMUOKZUTVBNZUMUNUORULESJZVDVEETZBACDEFGHUAUB
      UCULUPUNVAFJZLVBVCNZUQUNVHULUMUNUOUDULUMUOVHUNULVFUMUOVHVGACDEFGHUEUFUGUH
      ULUNVHVIBVAEFGOUJUIUK $.

    $( Law for double group division.  (Contributed by NM, 29-Feb-2008.)
       (New usage is discouraged.) $)
    ablodivdiv $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
    ( A D ( B D C ) ) = ( ( A D B ) G C ) ) $=
      ( cablo wcel w3a wa co cgr wceq ablogrpo grpodivdiv 3ancomb grpomuldivass
      sylan ablomuldiv eqtr3d sylan2b eqtrd ) EIJZAFJZBFJZCFJZKZLABCDMDMZACBDME
      MZABDMCEMZUEENJZUIUJUKOEPZABCDEFGHQTUIUEUFUHUGKZUKULOUFUGUHRUEUOLACEMBDMZ
      UKULUEUMUOUPUKOUNACBDEFGHSTACBDEFGHUAUBUCUD $.

    $( Law for double group division.  (Contributed by NM, 29-Feb-2008.)
       (New usage is discouraged.) $)
    ablodivdiv4 $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
    ( ( A D B ) D C ) = ( A D ( B G C ) ) ) $=
      ( cablo wcel w3a wa co cgn cfv cgr wceq ablogrpo simpl grpodivcl syl3anc
      3adant3r3 simpr3 eqid grpodivval sylan simpr1 simpr2 simp3 grpoinvcl 3jca
      syl2an ablodivdiv syldan grpodivinv syl3an1 3adant3r1 oveq2d 3eqtr2d ) EI
      JZAFJZBFJZCFJZKZLZABDMZCDMZVFCENOZOZEMZABVIDMZDMZABCEMZDMUTEPJZVDVGVJQZER
      ZVNVDLVNVFFJZVCVOVNVDSVNVAVBVQVCABDEFGHTUBVNVAVBVCUCVFCDEVHFGVHUDZHUEUAUF
      UTVDVAVBVIFJZKVLVJQVEVAVBVSUTVAVBVCUGUTVAVBVCUHUTVNVCVSVDVPVAVBVCUICEVHFG
      VRUJULUKABVIDEFGHUMUNVEVKVMADUTVBVCVKVMQZVAUTVNVBVCVTVPBCDEVHFGVRHUOUPUQU
      RUS $.

    $( Swap the second and third terms in a double division.  (Contributed by
       NM, 29-Feb-2008.)  (New usage is discouraged.) $)
    ablodiv32 $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
   ( ( A D B ) D C ) = ( ( A D C ) D B ) ) $=
      ( cablo wcel w3a wa co wceq ablocom 3adant3r1 ablodivdiv4 3ancomb sylan2b
      oveq2d 3eqtr4d ) EIJZAFJZBFJZCFJZKZLZABCEMZDMACBEMZDMZABDMCDMACDMBDMZUGUH
      UIADUBUDUEUHUINUCBCEFGOPTABCDEFGHQUFUBUCUEUDKUKUJNUCUDUERACBDEFGHQSUA $.

    $( Cancellation law for group division.  ( ~ nncan analog.)  (Contributed
       by NM, 7-Mar-2008.)  (New usage is discouraged.) $)
    ablonncan $p |- ( ( G e. AbelOp /\ A e. X /\ B e. X ) ->
             ( A D ( A D B ) ) = B ) $=
      ( cablo wcel w3a co cgi cfv wceq wa id 3anidm12 ablodivdiv sylan2 sylan
      3impb cgr ablogrpo eqid grpodivid 3adant3 oveq1d grpolid 3adant2 3eqtrd )
      DHIZAEIZBEIZJZAABCKCKZAACKZBDKZDLMZBDKZBUKULUMUOUQNZULUMOUKULULUMJZUTULUM
      VAVAPQAABCDEFGRSUAUNUPURBDUKULUPURNZUMUKDUBIZULVBDUCZACURDEFGURUDZUETUFUG
      UKUMUSBNZULUKVCUMVFVDBURDEFVEUHTUIUJ $.

    $( Cancellation law for group division.  ( ~ nnncan1 analog.)  (Contributed
       by NM, 7-Mar-2008.)  (New usage is discouraged.) $)
    ablonnncan1 $p |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
         ( ( A D B ) D ( A D C ) ) = ( C D B ) ) $=
      ( cablo wcel w3a wa wceq simpr1 simpr2 cgr ablogrpo grpodivcl 3adant3r2
      co syl3an1 3jca ablodiv32 syldan ablonncan oveq1d eqtrd ) EIJZAFJZBFJZCFJ
      ZKZLZABDTACDTZDTZAUNDTZBDTZCBDTUHULUIUJUNFJZKUOUQMUMUIUJURUHUIUJUKNUHUIUJ
      UKOUHUIUKURUJUHEPJUIUKUREQACDEFGHRUASUBABUNDEFGHUCUDUMUPCBDUHUIUKUPCMUJAC
      DEFGHUESUFUG $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Complex vector spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CVecOLD $.

  $( Extend class notation with the class of all complex vector spaces. $)
  cvc $a class CVecOLD $.

  ${
    $d g s x y z $.
    $( Define the class of all complex vector spaces.  (Contributed by NM,
       3-Nov-2006.)  (New usage is discouraged.) $)
    df-vc $a |- CVecOLD = { <. g , s >. | ( g e. AbelOp /\
     s : ( CC X. ran g ) --> ran g /\ A. x e. ran g ( ( 1 s x ) = x /\
       A. y e. CC ( A. z e. ran g ( y s ( x g z ) ) = ( ( y s x ) g ( y s z ) )
         /\ A. z e. CC ( ( ( y + z ) s x ) = ( ( y s x ) g ( z s x ) ) /\
           ( ( y x. z ) s x ) = ( y s ( z s x ) ) ) ) ) ) } $.

    $( The class of all complex vector spaces is a relation.  (Contributed by
       NM, 17-Mar-2007.)  (New usage is discouraged.) $)
    vcrel $p |- Rel CVecOLD $=
      ( vg vs vx vy vz cv cablo wcel cc crn cxp wf c1 co wceq wral caddc wa w3a
      cmul cvc df-vc relopabiv ) AFZGHIUDJZKUEBFZLMCFZUFNUGODFZUGEFZUDNUFNUHUGU
      FNZUHUIUFNUDNOEUEPUHUIQNUGUFNUJUIUGUFNZUDNOUHUITNUGUFNUHUKUFNOREIPRDIPRCU
      EPSABUACDEABUBUC $.
  $}

  ${
    $d g s x y z G $.  $d g s x y z S $.  $d g s W $.  $d g s x y z X $.
    $d x y z A $.  $d x y z B $.  $d x y z C $.
    vciOLD.1 $e |- G = ( 1st ` W ) $.
    vciOLD.2 $e |- S = ( 2nd ` W ) $.
    vciOLD.3 $e |- X = ran G $.
    $( Obsolete version of ~ cvsi .  The properties of a complex vector space,
       which is an Abelian group (i.e. the vectors, with the operation of
       vector addition) accompanied by a scalar multiplication operation on the
       field of complex numbers.  The variable ` W ` was chosen because ` _V `
       is already used for the universal class.  (Contributed by NM,
       3-Nov-2006.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    vciOLD $p |- ( W e. CVecOLD ->
              ( G e. AbelOp /\
         S : ( CC X. X ) --> X /\ A. x e. X ( ( 1 S x ) = x /\
       A. y e. CC ( A. z e. X ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) )
         /\ A. z e. CC ( ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) /\
           ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) ) ) ) ) $=
      ( vg vs cc cv co wceq wral wa oveq ralbidv cablo wcel cxp wf c1 caddc w3a
      cmul crn copab cvc c1st cfv wb eqeq2i eleq1 rneq eqtr4di xpeq2 feq2d feq3
      bitrd syl oveq2d eqeq12d raleqbidv eqeq2d anbi1d anbi12d anbi2d 3anbi123d
      sylbir c2nd feq1 eqeq1d oveq12d eqtrd 3anbi23d elopabi df-vc eleq2s ) EUA
      UBZMGUCZGDUDZUEANZDOZWEPZBNZWECNZEOZDOZWHWEDOZWHWIDOZEOZPZCGQZWHWIUFOZWED
      OZWLWIWEDOZEOZPZWHWIUHOZWEDOZWHWSDOZPZRZCMQZRZBMQZRZAGQZUGZFKNZUAUBZMXMUI
      ZUCZXOLNZUDZUEWEXQOZWEPZWHWEWIXMOZXQOZWHWEXQOZWHWIXQOZXMOZPZCXOQZWQWEXQOZ
      YCWIWEXQOZXMOZPZXBWEXQOZWHYIXQOZPZRZCMQZRZBMQZRZAXOQZUGZKLUJUKUUAWBWCGXQU
      DZXTWHWJXQOZYCYDEOZPZCGQZYHYCYIEOZPZYNRZCMQZRZBMQZRZAGQZUGZXLKLFXMFULUMZP
      XMEPZUUAUUOUNEUUPXMHUOUUQXNWBXRUUBYTUUNXMEUAUPUUQXOGPZXRUUBUNUUQXOEUIGXME
      UQJURZUURXRWCXOXQUDUUBUURXPWCXOXQXOGMUSUTXOGWCXQVAVBVCUUQYSUUMAXOGUUSUUQY
      RUULXTUUQYQUUKBMUUQYGUUFYPUUJUUQYFUUECXOGUUSUUQYBUUCYEUUDUUQYAWJWHXQWEWIX
      MESVDYCYDXMESVEVFUUQYOUUICMUUQYKUUHYNUUQYJUUGYHYCYIXMESVGVHTVITVJVFVKVLXQ
      FVMUMZPXQDPZUUOXLUNDUUTXQIUOUVAUUBWDUUNXKWBWCGXQDVNUVAUUMXJAGUVAXTWGUULXI
      UVAXSWFWEUEWEXQDSVOUVAUUKXHBMUVAUUFWPUUJXGUVAUUEWOCGUVAUUCWKUUDWNWHWJXQDS
      UVAYCWLYDWMEWHWEXQDSZWHWIXQDSVPVETUVAUUIXFCMUVAUUHXAYNXEUVAYHWRUUGWTWQWEX
      QDSUVAYCWLYIWSEUVBWIWEXQDSZVPVEUVAYLXCYMXDXBWEXQDSUVAYMWHWSXQOXDUVAYIWSWH
      XQUVCVDWHWSXQDSVQVEVITVITVITVRVLVSABCKLVTWA $.

    $( Functionality of th scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vcsm $p |- ( W e. CVecOLD -> S : ( CC X. X ) --> X ) $=
      ( vx vy vz cvc wcel cablo cc cxp cv co wceq wral wa wf cmul vciOLD simp2d
      c1 caddc ) CKLBMLNDODAUAUEHPZAQUGRIPZUGJPZBQAQUHUGAQZUHUIAQBQRJDSUHUIUFQU
      GAQUJUIUGAQZBQRUHUIUBQUGAQUHUKAQRTJNSTINSTHDSHIJABCDEFGUCUD $.

    $( Closure of the scalar product of a complex vector space.  (Contributed
       by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vccl $p |- ( ( W e. CVecOLD /\ A e. CC /\ B e. X ) -> ( A S B ) e. X ) $=
      ( cvc wcel cc cxp wf co vcsm fovcdm syl3an1 ) EJKLFMFCNALKBFKABCOFKCDEFGH
      IPABFLFCQR $.

    $( Identity element for the scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  Obsolete theorem, use ~ clmvs1
       together with ~ cvsclm instead.  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    vcidOLD $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( 1 S A ) = A ) $=
      ( vx vy vz cvc wcel c1 cv co wceq wral cc wa cablo cxp wf cmul w3a vciOLD
      caddc simpl ralimi 3ad2ant3 syl oveq2 id eqeq12d rspccva sylan ) DLMZNIOZ
      BPZURQZIERZAEMNABPZAQZUQCUAMZSEUBEBUCZUTJOZURKOZCPBPVFURBPZVFVGBPCPQKERVF
      VGUGPURBPVHVGURBPZCPQVFVGUDPURBPVFVIBPQTKSRTJSRZTZIERZUEVAIJKBCDEFGHUFVLV
      DVAVEVKUTIEUTVJUHUIUJUKUTVCIAEURAQZUSVBURAURANBULVMUMUNUOUP $.

    $( Distributive law for the scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vcdi $p |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
       ( A S ( B G C ) ) = ( ( A S B ) G ( A S C ) ) ) $=
      ( vy vx vz cc wcel w3a co wceq wral oveq1 cvc wi cv cablo cxp wf c1 caddc
      cmul vciOLD simpl ralimi adantl 3ad2ant3 syl oveq2d oveq2 eqeq12d oveq12d
      wa oveq1d rspc3v syl5 3com12 impcom ) ANOZBGOZCGOZPFUAOZABCEQZDQZABDQZACD
      QZEQZRZVGVFVHVIVOUBVIKUCZLUCZMUCZEQZDQZVPVQDQZVPVRDQZEQZRZMGSZKNSZLGSZVGV
      FVHPVOVIEUDOZNGUEGDUFZUGVQDQVQRZWEVPVRUHQVQDQWAVRVQDQZEQRVPVRUIQVQDQVPWKD
      QRUTMNSZUTZKNSZUTZLGSZPWGLKMDEFGHIJUJWPWHWGWIWOWFLGWNWFWJWMWEKNWEWLUKULUM
      ULUNUOWDVOVPBVREQZDQZVPBDQZWBEQZRAWQDQZVLAVRDQZEQZRLKMBACGNGVQBRZVTWRWCWT
      XDVSWQVPDVQBVRETUPXDWAWSWBEVQBVPDUQVAURVPARZWRXAWTXCVPAWQDTXEWSVLWBXBEVPA
      BDTVPAVRDTUSURVRCRZXAVKXCVNXFWQVJADVRCBEUQUPXFXBVMVLEVRCADUQUPURVBVCVDVE
      $.

    $( Distributive law for the scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vcdir $p |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( ( A + B ) S C ) = ( ( A S C ) G ( B S C ) ) ) $=
      ( vy vz vx cc wcel caddc co wceq wral oveq2 w3a cvc wi cv cablo cxp wf c1
      cmul vciOLD simpl ralimi adantl 3ad2ant3 syl oveq12d eqeq12d oveq1 oveq1d
      wa oveq2d rspc3v syl5 3coml impcom ) ANOZBNOZCGOZUAFUBOZABPQZCDQZACDQZBCD
      QZEQZRZVHVFVGVIVOUCVIKUDZLUDZPQZMUDZDQZVPVSDQZVQVSDQZEQZRZLNSZKNSZMGSZVHV
      FVGUAVOVIEUEOZNGUFGDUGZUHVSDQVSRZVPVSVQEQDQWAVPVQDQEQRLGSZWDVPVQUIQVSDQVP
      WBDQRZUTZLNSZUTZKNSZUTZMGSZUAWGMKLDEFGHIJUJWRWHWGWIWQWFMGWPWFWJWOWEKNWNWE
      WKWMWDLNWDWLUKULUMULUMULUNUOWDVOVRCDQZVPCDQZVQCDQZEQZRAVQPQZCDQZVLXAEQZRM
      KLCABGNNVSCRZVTWSWCXBVSCVRDTXFWAWTWBXAEVSCVPDTVSCVQDTUPUQVPARZWSXDXBXEXGV
      RXCCDVPAVQPURUSXGWTVLXAEVPACDURUSUQVQBRZXDVKXEVNXHXCVJCDVQBAPTUSXHXAVMVLE
      VQBCDURVAUQVBVCVDVE $.

    $( Associative law for the scalar product of a complex vector space.
       (Contributed by NM, 3-Nov-2006.)  (New usage is discouraged.) $)
    vcass $p |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( ( A x. B ) S C ) = ( A S ( B S C ) ) ) $=
      ( vy vz vx cc wcel w3a cmul co wceq wral cvc wi cv cablo cxp wf c1 vciOLD
      caddc simpr ralimi adantl 3ad2ant3 syl oveq2 oveq2d eqeq12d oveq1d rspc3v
      wa oveq1 syl5 3coml impcom ) ANOZBNOZCGOZPFUAOZABQRZCDRZABCDRZDRZSZVGVEVF
      VHVMUBVHKUCZLUCZQRZMUCZDRZVNVOVQDRZDRZSZLNTZKNTZMGTZVGVEVFPVMVHEUDOZNGUEG
      DUFZUGVQDRVQSZVNVQVOERDRVNVQDRZVNVODRERSLGTZVNVOUIRVQDRWHVSERSZWAUTZLNTZU
      TZKNTZUTZMGTZPWDMKLDEFGHIJUHWPWEWDWFWOWCMGWNWCWGWMWBKNWLWBWIWKWALNWJWAUJU
      KULUKULUKUMUNWAVMVPCDRZVNVOCDRZDRZSAVOQRZCDRZAWRDRZSMKLCABGNNVQCSZVRWQVTW
      SVQCVPDUOXCVSWRVNDVQCVODUOUPUQVNASZWQXAWSXBXDVPWTCDVNAVOQVAURVNAWRDVAUQVO
      BSZXAVJXBVLXEWTVICDVOBAQUOURXEWRVKADVOBCDVAUPUQUSVBVCVD $.

    $( A vector plus itself is two times the vector.  (Contributed by NM,
       1-Feb-2007.)  Obsolete theorem, use ~ clmvs2 together with ~ cvsclm
       instead.  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    vc2OLD $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( A G A ) = ( 2 S A ) ) $=
      ( cvc wcel wa c1 co c2 vcidOLD oveq12d caddc df-2 oveq1i ax-1cn cc mpanr1
      wceq vcdir mp3anr1 eqtr2id eqtr3d ) DIJZAEJZKZLABMZUKCMZAACMNABMZUJUKAUKA
      CABCDEFGHOZUNPUJUMLLQMZABMZULNUOABRSUHLUAJZUIUPULUCZTUHUQUQUIURTLLABCDEFG
      HUDUEUBUFUG $.
  $}

  ${
    $d x y z G $.  $d x y z W $.
    vcabl.1 $e |- G = ( 1st ` W ) $.
    $( Vector addition is an Abelian group operation.  (Contributed by NM,
       3-Nov-2006.)  (New usage is discouraged.) $)
    vcablo $p |- ( W e. CVecOLD -> G e. AbelOp ) $=
      ( vx vy vz cvc wcel cablo cc crn cxp c2nd cfv cv co wceq wral wa eqid wf
      c1 caddc cmul vciOLD simp1d ) BGHAIHJAKZLUGBMNZUAUBDOZUHPUIQEOZUIFOZAPUHP
      UJUIUHPZUJUKUHPAPQFUGRUJUKUCPUIUHPULUKUIUHPZAPQUJUKUDPUIUHPUJUMUHPQSFJRSE
      JRSDUGRDEFUHABUGCUHTUGTUEUF $.

    $( Vector addition is a group operation.  (Contributed by NM, 4-Nov-2006.)
       (New usage is discouraged.) $)
    vcgrp $p |- ( W e. CVecOLD -> G e. GrpOp ) $=
      ( cvc wcel cablo cgr vcablo ablogrpo syl ) BDEAFEAGEABCHAIJ $.
  $}

  ${
    vclcan.1 $e |- G = ( 1st ` W ) $.
    vclcan.2 $e |- X = ran G $.
    $( Left cancellation law for vector addition.  (Contributed by NM,
       4-Nov-2006.)  (New usage is discouraged.) $)
    vclcan $p |- ( ( W e. CVecOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                  ( ( C G A ) = ( C G B ) <-> A = B ) ) $=
      ( cvc wcel cgr w3a co wceq wb vcgrp grpolcan sylan ) EIJDKJAFJBFJCFJLCADM
      CBDMNABNODEGPABCDFHQR $.
  $}

  ${
    vczcl.1 $e |- G = ( 1st ` W ) $.
    vczcl.2 $e |- X = ran G $.
    vczcl.3 $e |- Z = ( GId ` G ) $.
    $( The zero vector is a vector.  (Contributed by NM, 4-Nov-2006.)
       (New usage is discouraged.) $)
    vczcl $p |- ( W e. CVecOLD -> Z e. X ) $=
      ( cvc wcel cgr vcgrp grpoidcl syl ) BHIAJIDCIABEKDACFGLM $.

    $( The zero vector is a right identity element.  (Contributed by NM,
       4-Nov-2006.)  (New usage is discouraged.) $)
    vc0rid $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( A G Z ) = A ) $=
      ( cvc wcel cgr co wceq vcgrp grporid sylan ) CIJBKJADJAEBLAMBCFNAEBDGHOP
      $.
  $}

  ${
    vc0.1 $e |- G = ( 1st ` W ) $.
    vc0.2 $e |- S = ( 2nd ` W ) $.
    vc0.3 $e |- X = ran G $.
    vc0.4 $e |- Z = ( GId ` G ) $.
    $( Zero times a vector is the zero vector.  Equation 1a of [Kreyszig]
       p. 51.  (Contributed by NM, 4-Nov-2006.)  (New usage is discouraged.) $)
    vc0 $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( 0 S A ) = Z ) $=
      ( cvc wcel wa cc0 co wceq c1 vc0rid cc 0cn oveq1i mp3anr1 vcidOLD 3eqtr3a
      caddc 1p0e1 ax-1cn vcdir mpanr1 oveq1d 3eqtr2rd w3a wb vccl mp3an2 adantr
      vczcl simpr 3jca vclcan syldan mpbid ) DKLZAELZMZANABOZCOZAFCOZPZVFFPZVEV
      HAQABOZVFCOZVGACDEFGIJRVEQNUEOZABOZVKVLAVMQABUFUAVCNSLZVDVNVLPZTVCQSLVOVD
      VPUGQNABCDEGHIUHUBUIABCDEGHIUCZUDVEVKAVFCVQUJUKVCVDVFELZFELZVDULVIVJUMVEV
      RVSVDVCVOVDVRTNABCDEGHIUNUOVCVSVDCDEFGIJUQUPVCVDURUSVFFACDEGIUTVAVB $.

    $( Anything times the zero vector is the zero vector.  Equation 1b of
       [Kreyszig] p. 51.  (Contributed by NM, 24-Nov-2006.)
       (New usage is discouraged.) $)
    vcz $p |- ( ( W e. CVecOLD /\ A e. CC ) -> ( A S Z ) = Z ) $=
      ( cvc wcel cc wa cc0 cmul co wceq vczcl anim2i ancoms vcass mp3anr2 mul01
      0cn syldan oveq1d vc0 mpdan sylan9eqr oveq2d adantr 3eqtr3rd ) DKLZAMLZNA
      OPQZFBQZAOFBQZBQZFAFBQZUNUOUOFELZNZUQUSRZUOUNVBUNVAUOCDEFGIJSZTUAUNUOOMLV
      AVCUEAOFBCDEGHIUBUCUFUOUNUQURFUOUPOFBAUDUGUNVAURFRVDFBCDEFGHIJUHUIZUJUNUS
      UTRUOUNURFABVEUKULUM $.
  $}

  ${
    vcm.1 $e |- G = ( 1st ` W ) $.
    vcm.2 $e |- S = ( 2nd ` W ) $.
    vcm.3 $e |- X = ran G $.
    vcm.4 $e |- M = ( inv ` G ) $.
    $( Minus 1 times a vector is the underlying group's inverse element.
       Equation 2 of [Kreyszig] p. 51.  (Contributed by NM, 25-Nov-2006.)
       (New usage is discouraged.) $)
    vcm $p |- ( ( W e. CVecOLD /\ A e. X ) -> ( -u 1 S A ) = ( M ` A ) ) $=
      ( wcel c1 co cfv wceq cc neg1cn syl2anc cc0 eqtr3d cvc cneg cgi cgr vcgrp
      wa adantr vccl mp3an2 eqid grporid simpr grpoinvcl sylan grpoass syl13anc
      vcidOLD oveq2d caddc ax-1cn 1pneg1e0 addcomli oveq1i vcdir mp3anr1 mpanr1
      vc0 3eqtr3a oveq1d grporinv grpolid ) EUAKZAFKZUFZLUBZABMZCUCNZCMZVPADNZV
      NCUDKZVPFKZVRVPOVLVTVMCEGUEZUGZVLVOPKZVMWAQVOABCEFGHIUHUIZVPVQCFIVQUJZUKR
      VNVQVSCMZVRVSVNVPAVSCMZCMZWGVRVNVPACMZVSCMZWIWGVNVTWAVMVSFKZWKWIOWCWEVLVM
      ULVLVTVMWLWBACDFIJUMUNZVPAVSCFIUOUPVNWJVQVSCVNVPLABMZCMZWJVQVNWNAVPCABCEF
      GHIUQURVNVOLUSMZABMZSABMWOVQWPSABLVOSUTQVAVBVCVLLPKZVMWQWOOZUTVLWDWRVMWSQ
      VOLABCEFGHIVDVEVFABCEFVQGHIWFVGVHTVITVNWHVQVPCVLVTVMWHVQOWBAVQCDFIWFJVJUN
      URTVNVTWLWGVSOWCWMVSVQCFIWFVKRTT $.
  $}

  ${
    $d g s x y z G $.  $d g s x y z S $.  $d g s x z X $.
    isvclem.1 $e |- X = ran G $.
    $( Lemma for ~ isvcOLD .  (Contributed by NM, 31-May-2008.)
       (New usage is discouraged.) $)
    isvclem $p |- ( ( G e. _V /\ S e. _V ) -> ( <. G , S >. e. CVecOLD
     <-> ( G e. AbelOp /\ S : ( CC X. X ) --> X /\ A. x e. X ( ( 1 S x ) = x /\
       A. y e. CC ( A. z e. X ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) )
         /\ A. z e. CC ( ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) /\
           ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) ) ) ) ) ) $=
      ( vg vs wcel cv cc wf co wceq wral wa cvv oveq ralbidv cop cvc crn cxp c1
      cablo caddc cmul w3a copab df-vc eleq2i eleq1 wb rneq eqtr4di xpeq2 feq2d
      bitrd syl oveq2d eqeq12d raleqbidv eqeq2d anbi1d anbi12d anbi2d 3anbi123d
      feq3 feq1 eqeq1d oveq12d eqtrd 3anbi23d opelopabg bitrid ) EDUAZUBJVQHKZU
      FJZLVRUCZUDZVTIKZMZUEAKZWBNZWDOZBKZWDCKZVRNZWBNZWGWDWBNZWGWHWBNZVRNZOZCVT
      PZWGWHUGNZWDWBNZWKWHWDWBNZVRNZOZWGWHUHNZWDWBNZWGWRWBNZOZQZCLPZQZBLPZQZAVT
      PZUIZHIUJZJERJDRJQEUFJZLFUDZFDMZUEWDDNZWDOZWGWDWHENZDNZWGWDDNZWGWHDNZENZO
      ZCFPZWPWDDNZXTWHWDDNZENZOZXAWDDNZWGYFDNZOZQZCLPZQZBLPZQZAFPZUIZUBXLVQABCH
      IUKULXKXMXNFWBMZWFWGXRWBNZWKWLENZOZCFPZWQWKWRENZOZXDQZCLPZQZBLPZQZAFPZUIY
      RHIEDRRVREOZVSXMWCYSXJUUKVREUFUMUULVTFOZWCYSUNUULVTEUCFVREUOGUPZUUMWCXNVT
      WBMYSUUMWAXNVTWBVTFLUQURVTFXNWBVIUSUTUULXIUUJAVTFUUNUULXHUUIWFUULXGUUHBLU
      ULWOUUCXFUUGUULWNUUBCVTFUUNUULWJYTWMUUAUULWIXRWGWBWDWHVRESVAWKWLVRESVBVCU
      ULXEUUFCLUULWTUUEXDUULWSUUDWQWKWRVRESVDVETVFTVGVCVHWBDOZYSXOUUKYQXMXNFWBD
      VJUUOUUJYPAFUUOWFXQUUIYOUUOWEXPWDUEWDWBDSVKUUOUUHYNBLUUOUUCYDUUGYMUUOUUBY
      CCFUUOYTXSUUAYBWGXRWBDSUUOWKXTWLYAEWGWDWBDSZWGWHWBDSVLVBTUUOUUFYLCLUUOUUE
      YHXDYKUUOWQYEUUDYGWPWDWBDSUUOWKXTWRYFEUUPWHWDWBDSZVLVBUUOXBYIXCYJXAWDWBDS
      UUOXCWGWRDNYJWGWRWBDSUUOWRYFWGDUUQVAVMVBVFTVFTVFTVNVOVP $.
  $}

  $( The components of a complex vector space are sets.  (Contributed by NM,
     31-May-2008.)  (New usage is discouraged.) $)
  vcex $p |- ( <. G , S >. e. CVecOLD -> ( G e. _V /\ S e. _V ) ) $=
    ( cop cvc wcel wbr cvv wa df-br vcrel brrelex12i sylbir ) BACDEBADFBGEAGEHB
    ADIBADJKL $.

  ${
    $d x y z G $.  $d x y z S $.  $d x z X $.
    isvcOLD.1 $e |- X = ran G $.
    $( The predicate "is a complex vector space."  (Contributed by NM,
       31-May-2008.)  Obsolete version of ~ iscvsp .
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    isvcOLD $p |- ( <. G , S >. e. CVecOLD <-> ( G e. AbelOp /\
         S : ( CC X. X ) --> X /\ A. x e. X ( ( 1 S x ) = x /\
       A. y e. CC ( A. z e. X ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) )
         /\ A. z e. CC ( ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) /\
           ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) ) ) ) ) $=
      ( cop cvc wcel cvv wa cablo cc cxp cv co wceq wral cgr wf caddc cmul vcex
      c1 w3a elex adantr cnex ablogrpo crn rnexg eqeltrid syl xpexg sylancr fex
      sylan2 ancoms jca 3adant3 isvclem pm5.21nii ) EDHIJEKJZDKJZLZEMJZNFOZFDUA
      ZUEAPZDQVJRBPZVJCPZEQDQVKVJDQZVKVLDQEQRCFSVKVLUBQVJDQVMVLVJDQZEQRVKVLUCQV
      JDQVKVNDQRLCNSLBNSLAFSZUFDEUDVGVIVFVOVGVILVDVEVGVDVIEMUGUHVIVGVEVGVIVHKJZ
      VEVGNKJFKJZVPUIVGETJZVQEUJVRFEUKKGETULUMUNNFKKUOUPVHFKDUQURUSUTVAABCDEFGV
      BVC $.
  $}

  ${
    $d x y z G $.  $d x y z S $.  $d x y z X $.
    isvciOLD.1 $e |- G e. AbelOp $.
    isvciOLD.2 $e |- dom G = ( X X. X ) $.
    isvciOLD.3 $e |- S : ( CC X. X ) --> X $.
    isvciOLD.4 $e |- ( x e. X -> ( 1 S x ) = x ) $.
    isvciOLD.5 $e |- ( ( y e. CC /\ x e. X /\ z e. X ) ->
                  ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) ) ) $.
    isvciOLD.6 $e |- ( ( y e. CC /\ z e. CC /\ x e. X ) ->
                  ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) ) $.
    isvciOLD.7 $e |- ( ( y e. CC /\ z e. CC /\ x e. X ) ->
                  ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) $.
    isvciOLD.8 $e |- W = <. G , S >. $.
    $( Properties that determine a complex vector space.  (Contributed by NM,
       5-Nov-2006.)  Obsolete version of ~ iscvsi .
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    isvciOLD $p |- W e. CVecOLD $=
      ( wcel cc co wceq wral cop cvc cablo cxp wf c1 cv caddc cmul 3com12 3expa
      wa ralrimiva w3a jca 3comr rgen cgr ablogrpo ax-mp grporn isvcOLD eqeltri
      mpbir3an ) FEDUAZUBOVEUBPEUCPZQGUDGDUEUFAUGZDRVGSZBUGZVGCUGZERDRVIVGDRZVI
      VJDRERSZCGTZVIVJUHRVGDRVKVJVGDRZERSZVIVJUIRVGDRVIVNDRSZULZCQTZULZBQTZULZA
      GTHJWAAGVGGPZVHVTKWBVSBQWBVIQPZULZVMVRWDVLCGWBWCVJGPZVLWCWBWEVLLUJUKUMWDV
      QCQWBWCVJQPZVQWCWFWBVQWCWFWBUNVOVPMNUOUPUKUMUOUMUOUQABCDEGEGVFEURPHEUSUTI
      VAVBVDVC $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples of complex vector spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z $.
    $( Obsolete version of ~ cnaddabl .  Complex number addition is an Abelian
       group operation.  (Contributed by NM, 5-Nov-2006.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    cnaddabloOLD $p |- + e. AbelOp $=
      ( vx vy vz caddc cc cc0 cv cneg cnex ax-addf addass 0cn addlid negcl wcel
      co wceq addcom mpdan negid eqtr3d isgrpoi cxp fdmi isabloi ) ABDEABCFDAGZ
      HZEIJUFBGZCGKLUFMUFNZUFEOZUFUGDPZUGUFDPZFUJUGEOUKULQUIUFUGRSUFTUAUBEEUCED
      JUDUFUHRUE $.

    $( Obsolete version of ~ cnaddid .  The group identity element of complex
       number addition is zero.  (Contributed by Steve Rodriguez, 3-Dec-2006.)
       (Revised by Mario Carneiro, 21-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    cnidOLD $p |- 0 = ( GId ` + ) $=
      ( vy vx caddc cgi cfv cv co wceq cc wral crio cc0 wcel cablo cnaddabloOLD
      cgr ablogrpo ax-mp cxp ax-addf fdmi grporn eqid grpoidval addlid rgen 0cn
      wreu wb grpoideu oveq1 eqeq1d ralbidv riota2 mp2an mpbi eqtr2i ) CDEZAFZB
      FZCGZUTHZBIJZAIKZLCPMZURVDHCNMVEOCQRZBAURCICIVFIISICTUAUBZURUCUDRLUTCGZUT
      HZBIJZVDLHZVIBIUTUEUFLIMVCAIUHZVJVKUIUGVEVLVFBACIVGUJRVCVJAILUSLHZVBVIBIV
      MVAVHUTUSLUTCUKULUMUNUOUPUQ $.

    $( Obsolete version of ~ cncvs .  The set of complex numbers is a complex
       vector space.  The vector operation is ` + ` , and the scalar product is
       ` x. ` .  (Contributed by NM, 5-Nov-2006.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    cncvcOLD $p |- <. + , x. >. e. CVecOLD $=
      ( vx vy vz cmul caddc cop cc cnaddabloOLD cxp ax-addf fdmi ax-mulf mullid
      cv adddi adddir mulass eqid isvciOLD ) ABCDEEDFZGHGGIGEJKLANZMBNZUACNZOUB
      UCUAPUBUCUAQTRS $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Normed complex vector spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c NrmCVec $.

  $c +v $.
  $c BaseSet $.
  $c .sOLD $.
  $c 0vec $.
  $c -v $.
  $c normCV $.

  $c IndMet $.

  $( Extend class notation with the class of all normed complex vector
     spaces. $)
  cnv $a class NrmCVec $.

  $( Extend class notation with vector addition in a normed complex vector
     space.  In the literature, the subscript "v" is omitted, but we need it to
     avoid ambiguity with complex number addition ` + ` ~ caddc . $)
  cpv $a class +v $.

  $( Extend class notation with the base set of a normed complex vector space.
     (Note that ` BaseSet ` is capitalized because, once it is fixed for a
     particular vector space ` U ` , it is not a function, unlike e.g.,
     ` normCV ` .  This is our typical convention.)
     (New usage is discouraged.) $)
  cba $a class BaseSet $.

  $( Extend class notation with scalar multiplication in a normed complex
     vector space.  In the literature scalar multiplication is usually
     indicated by juxtaposition, but we need an explicit symbol to prevent
     ambiguity. $)
  cns $a class .sOLD $.

  $( Extend class notation with zero vector in a normed complex vector
     space. $)
  cn0v $a class 0vec $.

  $( Extend class notation with vector subtraction in a normed complex vector
     space. $)
  cnsb $a class -v $.

  $( Extend class notation with the norm function in a normed complex vector
     space.  In the literature, the norm of ` A ` is usually written "|| ` A `
     ||", but we use function notation to take advantage of our existing
     theorems about functions. $)
  cnmcv $a class normCV $.

  $( Extend class notation with the class of the induced metrics on normed
     complex vector spaces. $)
  cims $a class IndMet $.

  ${
    $d g s n u w x y $.  $d y N $.
    $( Define the class of all normed complex vector spaces.  (Contributed by
       NM, 11-Nov-2006.)  (New usage is discouraged.) $)
    df-nv $a |- NrmCVec = { <. <. g , s >. , n >. |
      ( <. g , s >. e. CVecOLD /\ n : ran g --> RR /\ A. x e. ran g
        ( ( ( n ` x ) = 0 -> x = ( GId ` g ) ) /\
          A. y e. CC ( n ` ( y s x ) ) = ( ( abs ` y ) x. ( n ` x ) ) /\
          A. y e. ran g ( n ` ( x g y ) ) <_ ( ( n ` x ) + ( n ` y ) ) ) ) } $.

    $( Structure of the class of all normed complex vectors spaces.
       (Contributed by NM, 28-Nov-2006.)  (Revised by Mario Carneiro,
       1-May-2015.)  (New usage is discouraged.) $)
    nvss $p |- NrmCVec C_ ( CVecOLD X. _V ) $=
      ( vw vg vs vn vx vy cv cop wceq cvc wcel cfv co wral w3a wa wex copab cvv
      cnv crn cr wf cc0 cgi wi cabs cmul cc caddc cle wbr cxp biimpar 3ad2antr1
      eleq1 exlimivv jctir ssopab2i coprab df-nv dfoprab2 eqtri df-xp 3sstr4i
      vex ) AGZBGZCGZHZIZVJJKZVHUAZUBDGZUCZEGZVNLZUDIVPVHUELIUFFGZVPVIMVNLVRUGL
      VQUHMIFUINVPVRVHMVNLVQVRVNLUJMUKULFVMNOEVMNZOZPZCQBQZADRZVGJKZVNSKZPZADRT
      JSUMWBWFADWBWDWEWAWDBCVKVOVLWDVSVKWDVLVGVJJUPUNUOUQDVFURUSTVTBCDUTWCEFBDC
      VAVTBCDAVBVCADJSVDVE $.

    $( A normed complex vector space is a vector space.  (Contributed by NM,
       5-Jun-2008.)  (Revised by Mario Carneiro, 1-May-2015.)
       (New usage is discouraged.) $)
    nvvcop $p |- ( <. W , N >. e. NrmCVec -> W e. CVecOLD ) $=
      ( cop cnv wcel cvc cvv cxp nvss sseli opelxp1 syl ) BACZDEMFGHZEBFEDNMIJB
      AFGKL $.

    $( Define vector addition on a normed complex vector space.  (Contributed
       by NM, 23-Apr-2007.)  (New usage is discouraged.) $)
    df-va $a |- +v = ( 1st o. 1st ) $.

    $( Define the base set of a normed complex vector space.  (Contributed by
       NM, 23-Apr-2007.)  (New usage is discouraged.) $)
    df-ba $a |- BaseSet = ( x e. _V |-> ran ( +v ` x ) ) $.

    $( Define scalar multiplication on a normed complex vector space.
       (Contributed by NM, 24-Apr-2007.)  (New usage is discouraged.) $)
    df-sm $a |- .sOLD = ( 2nd o. 1st ) $.

    $( Define the zero vector in a normed complex vector space.  (Contributed
       by NM, 24-Apr-2007.)  (New usage is discouraged.) $)
    df-0v $a |- 0vec = ( GId o. +v ) $.

    $( Define vector subtraction on a normed complex vector space.
       (Contributed by NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    df-vs $a |- -v = ( /g o. +v ) $.

    $( Define the norm function in a normed complex vector space.  (Contributed
       by NM, 25-Apr-2007.)  (New usage is discouraged.) $)
    df-nmcv $a |- normCV = 2nd $.

    $( Define the induced metric on a normed complex vector space.
       (Contributed by NM, 11-Sep-2007.)  (New usage is discouraged.) $)
    df-ims $a |- IndMet = ( u e. NrmCVec |->
                            ( ( normCV ` u ) o. ( -v ` u ) ) ) $.
  $}

  $( The class of all normed complex vectors spaces is a relation.
     (Contributed by NM, 14-Nov-2006.)  (New usage is discouraged.) $)
  nvrel $p |- Rel NrmCVec $=
    ( cnv cvc cvv cxp wss wrel nvss relxp relss mp2 ) ABCDZEKFAFGBCHAKIJ $.

  ${
    vafval.2 $e |- G = ( +v ` U ) $.
    $( Value of the function for the vector addition (group) operation on a
       normed complex vector space.  (Contributed by NM, 23-Apr-2007.)
       (New usage is discouraged.) $)
    vafval $p |- G = ( 1st ` ( 1st ` U ) ) $=
      ( cpv cfv c1st cvv wcel wceq df-va fveq1i wf wfo fo1st fof ax-mp fvco3 c0
      ccom fvprc mpan eqtrid wn fveq2d 1st0 eqtr2di eqtrd pm2.61i eqtri ) BADEZ
      AFEZFEZCAGHZUJULIUMUJAFFSZEZULADUNJKGGFLZUMUOULIGGFMUPNGGFOPGGAFFQUAUBUMU
      CZUJRULADTUQULRFERUQUKRFAFTUDUEUFUGUHUI $.
  $}

  ${
    $d u U $.
    bafval.1 $e |- X = ( BaseSet ` U ) $.
    bafval.2 $e |- G = ( +v ` U ) $.
    $( Value of the function for the base set of a normed complex vector space.
       (Contributed by NM, 23-Apr-2007.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    bafval $p |- X = ran G $=
      ( vu cba cfv cpv crn cvv wcel wceq cv fveq2 rneqd df-ba fvex c0 fvprc rn0
      rnex fvmpt wn eqcomi 3eqtr4a pm2.61i rneqi 3eqtr4i ) AGHZAIHZJZCBJAKLZUJU
      LMFAFNZIHZJULKGUNAMUOUKUNAIOPFQUKAIRUBUCUMUDZSSJZUJULUQSUAUEAGTUPUKSAITPU
      FUGDBUKEUHUI $.
  $}

  ${
    smfval.4 $e |- S = ( .sOLD ` U ) $.
    $( Value of the function for the scalar multiplication operation on a
       normed complex vector space.  (Contributed by NM, 24-Apr-2007.)
       (New usage is discouraged.) $)
    smfval $p |- S = ( 2nd ` ( 1st ` U ) ) $=
      ( cns cfv c1st c2nd cvv wcel wceq ccom df-sm fveq1i wf wfo fo1st ax-mp c0
      fof fvprc fvco3 mpan eqtrid wn fveq2d 2nd0 eqtr2di eqtrd pm2.61i eqtri )
      ABDEZBFEZGEZCBHIZUKUMJUNUKBGFKZEZUMBDUOLMHHFNZUNUPUMJHHFOUQPHHFSQHHBGFUAU
      BUCUNUDZUKRUMBDTURUMRGERURULRGBFTUEUFUGUHUIUJ $.
  $}

  ${
    0vfval.2 $e |- G = ( +v ` U ) $.
    0vfval.5 $e |- Z = ( 0vec ` U ) $.
    $( Value of the function for the zero vector on a normed complex vector
       space.  (Contributed by NM, 24-Apr-2007.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.) $)
    0vfval $p |- ( U e. V -> Z = ( GId ` G ) ) $=
      ( wcel cvv cgi cfv wceq elex cpv ccom wfn c1st crn wss wfo cn0v fo1st ssv
      fofn ax-mp fnco mp3an df-va fneq1i mpbir fvco2 df-0v fveq1i eqtri 3eqtr4g
      mpan fveq2i syl ) ACGAHGZDBIJZKACLURAIMNZJZAMJZIJZDUSMHOZURVAVCKVDPPNZHOZ
      PHOZVGPQZHRVFHHPSVGUAHHPUCUDZVIVHUBHHPPUEUFHMVEUGUHUIHIMAUJUODATJVAFATUTU
      KULUMBVBIEUPUNUQ $.
  $}

  ${
    nmfval.6 $e |- N = ( normCV ` U ) $.
    $( Value of the norm function in a normed complex vector space.
       (Contributed by NM, 25-Apr-2007.)  (New usage is discouraged.) $)
    nmcvfval $p |- N = ( 2nd ` U ) $=
      ( cnmcv cfv c2nd df-nmcv fveq1i eqtri ) BADEAFECADFGHI $.
  $}

  ${
    nvop2.1 $e |- W = ( 1st ` U ) $.
    nvop2.6 $e |- N = ( normCV ` U ) $.
    $( A normed complex vector space is an ordered pair of a vector space and a
       norm operation.  (Contributed by NM, 28-Nov-2006.)
       (New usage is discouraged.) $)
    nvop2 $p |- ( U e. NrmCVec -> U = <. W , N >. ) $=
      ( cnv wcel c1st cfv c2nd cop wrel wceq nvrel 1st2nd mpan nmcvfval opeq12i
      eqtr4di ) AFGZAAHIZAJIZKZCBKFLTAUCMNAFOPCUABUBDABEQRS $.
  $}

  ${
    nvvop.1 $e |- W = ( 1st ` U ) $.
    nvvop.2 $e |- G = ( +v ` U ) $.
    nvvop.4 $e |- S = ( .sOLD ` U ) $.
    $( The vector space component of a normed complex vector space is an
       ordered pair of the underlying group and a scalar product.  (Contributed
       by NM, 28-Nov-2006.)  (New usage is discouraged.) $)
    nvvop $p |- ( U e. NrmCVec -> W = <. G , S >. ) $=
      ( cnv wcel c1st cfv c2nd cop cvc wrel wceq vcrel cvv fveq2i eqtr4i eleq1d
      cnmcv cxp nvss eqid nvop2 ibi sselid opelxp1 1st2nd sylancr vafval smfval
      syl opeq12i eqtr4di ) BHIZDDJKZDLKZMZCAMUQNODNIZDUTPQUQDBUBKZMZNRUCZIVAUQ
      HVDVCUDUQVCHIUQBVCHBVBDEVBUEUFUAUGUHDVBNRUIUNDNUJUKCURAUSCBJKZJKURBCFULDV
      EJESTAVELKUSABGUMDVELESTUOUP $.
  $}

  ${
    $d g n s x y G $.  $d g n s x y N $.  $d g n s x y S $.  $d g n s x y X $.
    $d g n s Z $.
    isnvlem.1 $e |- X = ran G $.
    isnvlem.2 $e |- Z = ( GId ` G ) $.
    $( Lemma for ~ isnv .  (Contributed by NM, 11-Nov-2006.)
       (New usage is discouraged.) $)
    isnvlem $p |- ( ( G e. _V /\ S e. _V /\ N e. _V ) ->
                 ( <. <. G , S >. , N >. e. NrmCVec <-> ( <. G , S >. e.
        CVecOLD
        /\ N : X --> RR /\ A. x e. X ( ( ( N ` x ) = 0 -> x = Z )
           /\ A. y e. CC ( N ` ( y S x ) ) = ( ( abs ` y ) x. ( N ` x ) ) /\
           A. y e. X ( N ` ( x G y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) ) ) ) $=
      ( wcel cv cvc cr cfv wceq co cc wral w3a cvv vg vs vn cop cnv crn cc0 cgi
      wf wi cabs cmul caddc cle wbr coprab df-nv eleq2i opeq1 eleq1d rneq feq2d
      fveq2 eqeq2d imbi2d oveq fveq2d breq1d raleqbidv 3anbi13d 3anbi123d opeq2
      eqtr4di fveqeq2d ralbidv 3anbi2d feq1 fveq1 eqeq1d imbi1d eqeq12d oveq12d
      oveq2d breq12d 3anbi23d eloprabg bitrid ) DCUDZEUDZUEJWIUAKZUBKZUDZLJZWJU
      FZMUCKZUIZAKZWONZUGOZWQWJUHNZOZUJZBKZWQWKPZWONXCUKNZWRULPZOZBQRZWQXCWJPZW
      ONZWRXCWONZUMPZUNUOZBWNRZSZAWNRZSZUAUBUCUPZJDTJCTJETJSWHLJZFMEUIZWQENZUGO
      ZWQGOZUJZXCWQCPZENZXEYAULPZOZBQRZWQXCDPZENZYAXCENZUMPZUNUOZBFRZSZAFRZSZUE
      XRWIABUAUCUBUQURXQDWKUDZLJZFMWOUIZWSYCUJZXHYJWONZXLUNUOZBFRZSZAFRZSXSUUAU
      UBYEWONZXFOZBQRZUUESZAFRZSYRUAUBUCDCETTTWJDOZWMYTWPUUAXPUUGUUMWLYSLWJDWKU
      SUTUUMWNFMWOUUMWNDUFFWJDVAHVMZVBUUMXOUUFAWNFUUNUUMXBUUBXNUUEXHUUMXAYCWSUU
      MWTGWQUUMWTDUHNGWJDUHVCIVMVDVEUUMXMUUDBWNFUUNUUMXJUUCXLUNUUMXIYJWOWQXCWJD
      VFVGVHVIVJVIVKWKCOZYTXSUUGUULUUAUUOYSWHLWKCDVLUTUUOUUFUUKAFUUOXHUUJUUBUUE
      UUOXGUUIBQUUOXDYEXFWOXCWQWKCVFVNVOVPVOVJWOEOZUUAXTUULYQXSFMWOEVQUUPUUKYPA
      FUUPUUBYDUUJYIUUEYOUUPWSYBYCUUPWRYAUGWQWOEVRZVSVTUUPUUIYHBQUUPUUHYFXFYGYE
      WOEVRUUPWRYAXEULUUQWCWAVOUUPUUDYNBFUUPUUCYKXLYMUNYJWOEVRUUPWRYAXKYLUMUUQX
      CWOEVRWBWDVOVKVOWEWFWG $.
  $}

  $( The components of a normed complex vector space are sets.  (Contributed by
     NM, 5-Jun-2008.)  (Revised by Mario Carneiro, 1-May-2015.)
     (New usage is discouraged.) $)
  nvex $p |- ( <. <. G , S >. , N >. e. NrmCVec
          -> ( G e. _V /\ S e. _V /\ N e. _V ) ) $=
    ( cop cnv wcel cvv wa w3a cvc nvvcop vcex syl cxp nvss sseli opelxp2 df-3an
    sylanbrc ) BADZCDZEFZBGFZAGFZHZCGFZUCUDUFIUBTJFUECTKABLMUBUAJGNZFUFEUGUAOPT
    CJGQMUCUDUFRS $.

  ${
    $d x y G $.  $d x y N $.  $d x y S $.  $d x y X $.
    isnv.1 $e |- X = ran G $.
    isnv.2 $e |- Z = ( GId ` G ) $.
    $( The predicate "is a normed complex vector space."  (Contributed by NM,
       5-Jun-2008.)  (New usage is discouraged.) $)
    isnv $p |- ( <. <. G , S >. , N >. e. NrmCVec <-> ( <. G , S >. e. CVecOLD
        /\ N : X --> RR /\ A. x e. X ( ( ( N ` x ) = 0 -> x = Z )
           /\ A. y e. CC ( N ` ( y S x ) ) = ( ( abs ` y ) x. ( N ` x ) ) /\
           A. y e. X ( N ` ( x G y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) ) ) $=
      ( cop wcel cvv w3a cr cv cfv wceq co wral wa cnv cvc wf cc0 wi cabs caddc
      cmul cc cle wbr nvex vcex adantr crn simpld rnexg syl eqeltrid fex sylan2
      ancoms df-3an sylanbrc 3adant3 isnvlem pm5.21nii ) DCJZEJUAKDLKZCLKZELKZM
      ZVHUBKZFNEUCZAOZEPZUDQVOGQUEBOZVOCREPVQUFPVPUHRQBUISVOVQDREPVPVQEPUGRUJUK
      BFSMAFSZMCDEULVMVNVLVRVMVNTVIVJTZVKVLVMVSVNCDUMZUNVNVMVKVMVNFLKVKVMFDUOZL
      HVMVIWALKVMVIVJVTUPDLUQURUSFNLEUTVAVBVIVJVKVCVDVEABCDEFGHIVFVG $.
  $}

  ${
    $d x y G $.  $d x y N $.  $d x y S $.  $d x y X $.
    isnvi.5 $e |- X = ran G $.
    isnvi.6 $e |- Z = ( GId ` G ) $.
    isnvi.7 $e |- <. G , S >. e. CVecOLD $.
    isnvi.8 $e |- N : X --> RR $.
    isnvi.9 $e |- ( ( x e. X /\ ( N ` x ) = 0 ) -> x = Z ) $.
    isnvi.10 $e |- ( ( y e. CC /\ x e. X ) ->
                    ( N ` ( y S x ) ) = ( ( abs ` y ) x. ( N ` x ) ) ) $.
    isnvi.11 $e |- ( ( x e. X /\ y e. X ) ->
                    ( N ` ( x G y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) $.
    isnvi.12 $e |- U = <. <. G , S >. , N >. $.
    $( Properties that determine a normed complex vector space.  (Contributed
       by NM, 15-Apr-2007.)  (New usage is discouraged.) $)
    isnvi $p |- U e. NrmCVec $=
      ( wcel cfv wceq co cop cnv cvc cr wf cv cc0 wi cabs cmul cc caddc cle wbr
      wral w3a ex ancoms ralrimiva 3jca rgen isnv mpbir3an eqeltri ) DECUAZFUAZ
      UBPVFUBQVEUCQGUDFUEAUFZFRZUGSZVGHSZUHZBUFZVGCTFRVLUIRVHUJTSZBUKUOZVGVLETF
      RVHVLFRULTUMUNZBGUOZUPZAGUOKLVQAGVGGQZVKVNVPVRVIVJMUQVRVMBUKVLUKQVRVMNURU
      SVRVOBGOUSUTVAABCEFGHIJVBVCVD $.
  $}

  ${
    $d x y G $.  $d x y N $.  $d x U $.  $d x y S $.  $d x y X $.
    nvi.1 $e |- X = ( BaseSet ` U ) $.
    nvi.2 $e |- G = ( +v ` U ) $.
    nvi.4 $e |- S = ( .sOLD ` U ) $.
    nvi.5 $e |- Z = ( 0vec ` U ) $.
    nvi.6 $e |- N = ( normCV ` U ) $.
    $( The properties of a normed complex vector space, which is a vector space
       accompanied by a norm.  (Contributed by NM, 11-Nov-2006.)  (Revised by
       Mario Carneiro, 21-Dec-2013.)  (New usage is discouraged.) $)
    nvi $p |- ( U e. NrmCVec -> ( <. G , S >. e. CVecOLD /\ N : X --> RR /\
       A. x e. X ( ( ( N ` x ) = 0 -> x = Z )
           /\ A. y e. CC ( N ` ( y S x ) ) = ( ( abs ` y ) x. ( N ` x ) ) /\
              A. y e. X ( N ` ( x G y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) ) ) $=
      ( cnv wcel cfv wceq co wral w3a cop cvc cr wf cv cc0 wi cabs cc caddc cle
      cmul wbr c1st eqid nvop2 nvvop opeq1d eqtrd id eqeltrrd bafval isnv sylib
      cgi 0vfval eqeq2d imbi2d 3anbi1d ralbidv 3anbi3d mpbird ) DNOZECUAZUBOZGU
      CFUDZAUEZFPZUFQZVQHQZUGZBUEZVQCRFPWBUHPVRULRQBUISZVQWBERFPVRWBFPUJRUKUMBG
      SZTZAGSZTVOVPVSVQEVEPZQZUGZWCWDTZAGSZTZVMVNFUAZNOWLVMDWMNVMDDUNPZFUAWMDFW
      NWNUOZMUPVMWNVNFCDEWNWOJKUQURUSVMUTVAABCEFGWGDEGIJVBWGUOVCVDVMWFWKVOVPVMW
      EWJAGVMWAWIWCWDVMVTWHVSVMHWGVQDENHJLVFVGVHVIVJVKVL $.
  $}

  ${
    $d x y U $.  $d x y W $.
    nvvc.1 $e |- W = ( 1st ` U ) $.
    $( The vector space component of a normed complex vector space.
       (Contributed by NM, 28-Nov-2006.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.) $)
    nvvc $p |- ( U e. NrmCVec -> W e. CVecOLD ) $=
      ( vx vy cnv wcel cpv cfv cns cop cvc eqid nvvop cba cr cv wceq co wral wf
      cnmcv cc0 cn0v wi cabs cmul cc caddc cle wbr w3a nvi simp1d eqeltrd ) AFG
      ZBAHIZAJIZKZLURAUQBCUQMZURMZNUPUSLGAOIZPAUBIZUADQZVCIZUCRVDAUDIZRUEEQZVDU
      RSVCIVGUFIVEUGSREUHTVDVGUQSVCIVEVGVCIUISUJUKEVBTULDVBTDEURAUQVCVBVFVBMUTV
      AVFMVCMUMUNUO $.
  $}

  ${
    nvabl.1 $e |- G = ( +v ` U ) $.
    $( The vector addition operation of a normed complex vector space is an
       Abelian group.  (Contributed by NM, 15-Feb-2008.)
       (New usage is discouraged.) $)
    nvablo $p |- ( U e. NrmCVec -> G e. AbelOp ) $=
      ( cnv wcel c1st cfv cvc cablo eqid nvvc vafval vcablo syl ) ADEAFGZHEBIEA
      OOJKBOABCLMN $.

    $( The vector addition operation of a normed complex vector space is a
       group.  (Contributed by NM, 15-Feb-2008.)
       (New usage is discouraged.) $)
    nvgrp $p |- ( U e. NrmCVec -> G e. GrpOp ) $=
      ( cnv wcel cablo cgr nvablo ablogrpo syl ) ADEBFEBGEABCHBIJ $.
  $}

  ${
    nvgf.1 $e |- X = ( BaseSet ` U ) $.
    nvgf.2 $e |- G = ( +v ` U ) $.
    $( Mapping for the vector addition operation.  (Contributed by NM,
       28-Jan-2008.)  (New usage is discouraged.) $)
    nvgf $p |- ( U e. NrmCVec -> G : ( X X. X ) --> X ) $=
      ( cnv wcel cgr cxp wfo wf nvgrp bafval grpofo fof 3syl ) AFGBHGCCIZCBJQCB
      KABELBCABCDEMNQCBOP $.
  $}

  ${
    nvsf.1 $e |- X = ( BaseSet ` U ) $.
    nvsf.4 $e |- S = ( .sOLD ` U ) $.
    $( Mapping for the scalar multiplication operation.  (Contributed by NM,
       28-Jan-2008.)  (New usage is discouraged.) $)
    nvsf $p |- ( U e. NrmCVec -> S : ( CC X. X ) --> X ) $=
      ( cnv wcel c1st cfv cvc cc cxp wf eqid nvvc cpv vafval smfval bafval vcsm
      syl ) BFGBHIZJGKCLCAMBUBUBNOABPIZUBCBUCUCNZQABERBUCCDUDSTUA $.
  $}

  ${
    nvgcl.1 $e |- X = ( BaseSet ` U ) $.
    nvgcl.2 $e |- G = ( +v ` U ) $.
    $( Closure law for the vector addition (group) operation of a normed
       complex vector space.  (Contributed by NM, 23-Apr-2007.)
       (New usage is discouraged.) $)
    nvgcl $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                    ( A G B ) e. X ) $=
      ( cnv wcel cgr co nvgrp bafval grpocl syl3an1 ) CHIDJIAEIBEIABDKEICDGLABD
      ECDEFGMNO $.

    $( The vector addition (group) operation is commutative.  (Contributed by
       NM, 4-Dec-2007.)  (New usage is discouraged.) $)
    nvcom $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                ( A G B ) = ( B G A ) ) $=
      ( cnv wcel cablo co wceq nvablo bafval ablocom syl3an1 ) CHIDJIAEIBEIABDK
      BADKLCDGMABDECDEFGNOP $.

    $( The vector addition (group) operation is associative.  (Contributed by
       NM, 4-Dec-2007.)  (New usage is discouraged.) $)
    nvass $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
              ( ( A G B ) G C ) = ( A G ( B G C ) ) ) $=
      ( cnv wcel cgr w3a co wceq nvgrp bafval grpoass sylan ) DIJEKJAFJBFJCFJLA
      BEMCEMABCEMEMNDEHOABCEFDEFGHPQR $.

    $( Commutative/associative law for vector addition.  (Contributed by NM,
       27-Dec-2007.)  (New usage is discouraged.) $)
    nvadd32 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( ( A G B ) G C ) = ( ( A G C ) G B ) ) $=
      ( cnv wcel cablo w3a co wceq nvablo bafval ablo32 sylan ) DIJEKJAFJBFJCFJ
      LABEMCEMACEMBEMNDEHOABCEFDEFGHPQR $.

    $( Right cancellation law for vector addition.  (Contributed by NM,
       4-Dec-2007.)  (New usage is discouraged.) $)
    nvrcan $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                  ( ( A G C ) = ( B G C ) <-> A = B ) ) $=
      ( cnv wcel cgr w3a co wceq wb nvgrp bafval grporcan sylan ) DIJEKJAFJBFJC
      FJLACEMBCEMNABNODEHPABCEFDEFGHQRS $.

    $( Rearrangement of 4 terms in a vector sum.  (Contributed by NM,
       8-Feb-2008.)  (New usage is discouraged.) $)
    nvadd4 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X ) /\ ( C e. X /\
       D e. X ) ) -> ( ( A G B ) G ( C G D ) ) = ( ( A G C ) G ( B G D ) ) ) $=
      ( cnv wcel cablo wa co wceq nvablo bafval ablo4 syl3an1 ) EJKFLKAGKBGKMCG
      KDGKMABFNCDFNFNACFNBDFNFNOEFIPABCDFGEFGHIQRS $.
  $}

  ${
    nvscl.1 $e |- X = ( BaseSet ` U ) $.
    nvscl.4 $e |- S = ( .sOLD ` U ) $.
    $( Closure law for the scalar product operation of a normed complex vector
       space.  (Contributed by NM, 1-Feb-2007.)  (New usage is discouraged.) $)
    nvscl $p |- ( ( U e. NrmCVec /\ A e. CC /\ B e. X ) ->
                       ( A S B ) e. X ) $=
      ( cnv wcel c1st cfv cvc cc co eqid nvvc cpv vafval smfval bafval syl3an1
      vccl ) DHIDJKZLIAMIBEIABCNEIDUCUCOPABCDQKZUCEDUDUDOZRCDGSDUDEFUETUBUA $.

    $( Identity element for the scalar product of a normed complex vector
       space.  (Contributed by NM, 4-Dec-2007.)  (New usage is discouraged.) $)
    nvsid $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( 1 S A ) = A ) $=
      ( cnv wcel c1st cfv cvc c1 co wceq eqid nvvc cpv vafval smfval bafval
      vcidOLD sylan ) CGHCIJZKHADHLABMANCUCUCOPABCQJZUCDCUDUDOZRBCFSCUDDEUETUAU
      B $.

    $( Associative law for the scalar product of a normed complex vector space.
       (Contributed by NM, 17-Nov-2007.)  (New usage is discouraged.) $)
    nvsass $p |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( ( A x. B ) S C ) = ( A S ( B S C ) ) ) $=
      ( cnv wcel c1st cfv cvc cc w3a cmul co wceq eqid nvvc vafval smfval vcass
      cpv bafval sylan ) EIJEKLZMJANJBNJCFJOABPQCDQABCDQDQREUGUGSTABCDEUDLZUGFE
      UHUHSZUADEHUBEUHFGUIUEUCUF $.

    $( Commutative law for the scalar product of a normed complex vector space.
       (Contributed by NM, 14-Feb-2008.)  (New usage is discouraged.) $)
    nvscom $p |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( A S ( B S C ) ) = ( B S ( A S C ) ) ) $=
      ( cnv wcel cc w3a wa cmul co wceq mulcom oveq1d 3adant3 nvsass 3ancoma
      adantl sylan2b 3eqtr3d ) EIJZAKJZBKJZCFJZLZMABNOZCDOZBANOZCDOZABCDODOBACD
      ODOZUIUKUMPZUEUFUGUOUHUFUGMUJULCDABQRSUBABCDEFGHTUIUEUGUFUHLUMUNPUFUGUHUA
      BACDEFGHTUCUD $.
  $}

  ${
    nvdi.1 $e |- X = ( BaseSet ` U ) $.
    nvdi.2 $e |- G = ( +v ` U ) $.
    nvdi.4 $e |- S = ( .sOLD ` U ) $.
    $( Distributive law for the scalar product of a complex vector space.
       (Contributed by NM, 4-Dec-2007.)  (New usage is discouraged.) $)
    nvdi $p |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
       ( A S ( B G C ) ) = ( ( A S B ) G ( A S C ) ) ) $=
      ( cnv wcel c1st cfv cvc cc w3a co wceq eqid nvvc vafval smfval vcdi sylan
      bafval ) EKLEMNZOLAPLBGLCGLQABCFRDRABDRACDRFRSEUGUGTUAABCDFUGGEFIUBDEJUCE
      FGHIUFUDUE $.

    $( Distributive law for the scalar product of a complex vector space.
       (Contributed by NM, 4-Dec-2007.)  (New usage is discouraged.) $)
    nvdir $p |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
      ( ( A + B ) S C ) = ( ( A S C ) G ( B S C ) ) ) $=
      ( cnv wcel c1st cfv cvc cc w3a caddc co wceq eqid nvvc vafval vcdir sylan
      smfval bafval ) EKLEMNZOLAPLBPLCGLQABRSCDSACDSBCDSFSTEUHUHUAUBABCDFUHGEFI
      UCDEJUFEFGHIUGUDUE $.

    $( A vector plus itself is two times the vector.  (Contributed by NM,
       9-Feb-2008.)  (New usage is discouraged.) $)
    nv2 $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( A G A ) = ( 2 S A ) ) $=
      ( cnv wcel c1st cfv cvc co c2 wceq eqid nvvc vafval smfval bafval vc2OLD
      sylan ) CIJCKLZMJAEJAADNOABNPCUDUDQRABDUDECDGSBCHTCDEFGUAUBUC $.
  $}

  ${
    $d g x y $.
    vsfval.2 $e |- G = ( +v ` U ) $.
    vsfval.3 $e |- M = ( -v ` U ) $.
    $( Value of the function for the vector subtraction operation on a normed
       complex vector space.  (Contributed by NM, 15-Feb-2008.)  (Revised by
       Mario Carneiro, 27-Dec-2014.)  (New usage is discouraged.) $)
    vsfval $p |- M = ( /g ` G ) $=
      ( vg vx vy cnsb cfv cpv cgs cvv wcel wceq wf c1st c0 cgr cv df-vs wfo fof
      ccom fveq1i fo1st ax-mp fco mp2an df-va feq1i mpbir fvco3 mpan eqtrid cdm
      wn 0ngrp crn cgn co cmpo vex rnex mpoex df-gdiv dmmpti eleq2i mtbir ndmfv
      mp1i fvprc fveq2d 3eqtr4rd pm2.61i fveq2i 3eqtr4i ) AIJZAKJZLJZCBLJAMNZVR
      VTOWAVRALKUDZJZVTAIWBUAUEMMKPZWAWCVTOWDMMQQUDZPZMMQPZWGWFMMQUBWGUFMMQUCUG
      ZWHMMMQQUHUIMMKWEUJUKULMMALKUMUNUOWAUQZRLJZRVTVRRLUPZNZUQWJROWIWLRSNURWKS
      RFSGHFTZUSZWNGTHTWMUTJJWMVAZVBLGHWNWNWOWMFVCVDZWPVEGHFVFVGVHVIRLVJVKWIVSR
      LAKVLVMAIVLVNVOEBVSLDVPVQ $.
  $}

  ${
    nvzcl.1 $e |- X = ( BaseSet ` U ) $.
    nvzcl.6 $e |- Z = ( 0vec ` U ) $.
    $( Closure law for the zero vector of a normed complex vector space.
       (Contributed by NM, 27-Nov-2007.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.) $)
    nvzcl $p |- ( U e. NrmCVec -> Z e. X ) $=
      ( cnv wcel cpv cfv cgi eqid 0vfval cgr nvgrp bafval grpoidcl syl eqeltrd
      ) AFGZCAHIZJIZBATFCTKZELSTMGUABGATUBNUATBATBDUBOUAKPQR $.
  $}

  ${
    nv0id.1 $e |- X = ( BaseSet ` U ) $.
    nv0id.2 $e |- G = ( +v ` U ) $.
    nv0id.6 $e |- Z = ( 0vec ` U ) $.
    $( The zero vector is a right identity element.  (Contributed by NM,
       28-Nov-2007.)  (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    nv0rid $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( A G Z ) = A ) $=
      ( cnv wcel wa co cgi cfv wceq 0vfval oveq2d adantr cgr nvgrp eqid grporid
      bafval sylan eqtrd ) BIJZADJZKAECLZACMNZCLZAUFUHUJOUGUFEUIACBCIEGHPQRUFCS
      JUGUJAOBCGTAUICDBCDFGUCUIUAUBUDUE $.

    $( The zero vector is a left identity element.  (Contributed by NM,
       28-Nov-2007.)  (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    nv0lid $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( Z G A ) = A ) $=
      ( cnv wcel wa co cgi cfv wceq 0vfval oveq1d adantr cgr nvgrp eqid grpolid
      bafval sylan eqtrd ) BIJZADJZKEACLZCMNZACLZAUFUHUJOUGUFEUIACBCIEGHPQRUFCS
      JUGUJAOBCGTAUICDBCDFGUCUIUAUBUDUE $.
  $}

  ${
    nv0.1 $e |- X = ( BaseSet ` U ) $.
    nv0.4 $e |- S = ( .sOLD ` U ) $.
    nv0.6 $e |- Z = ( 0vec ` U ) $.
    $( Zero times a vector is the zero vector.  (Contributed by NM,
       27-Nov-2007.)  (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    nv0 $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( 0 S A ) = Z ) $=
      ( cnv wcel wa cc0 co cpv cfv cgi c1st cvc wceq eqid nvvc vafval vc0 sylan
      smfval bafval 0vfval adantr eqtr4d ) CIJZADJZKLABMZCNOZPOZEUJCQOZRJUKULUN
      SCUOUOTUAABUMUODUNCUMUMTZUBBCGUECUMDFUPUFUNTUCUDUJEUNSUKCUMIEUPHUGUHUI $.
  $}

  ${
    nvsz.4 $e |- S = ( .sOLD ` U ) $.
    nvsz.6 $e |- Z = ( 0vec ` U ) $.
    $( Anything times the zero vector is the zero vector.  (Contributed by NM,
       28-Nov-2007.)  (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.) $)
    nvsz $p |- ( ( U e. NrmCVec /\ A e. CC ) -> ( A S Z ) = Z ) $=
      ( cnv wcel cc wa cpv cfv cgi co c1st cvc wceq eqid nvvc cba vafval smfval
      bafval vcz sylan 0vfval adantr oveq2d 3eqtr4d ) CGHZAIHZJZACKLZMLZBNZUNAD
      BNDUJCOLZPHUKUOUNQCUPUPRSABUMUPCTLZUNCUMUMRZUABCEUBCUMUQUQRURUCUNRUDUEULD
      UNABUJDUNQUKCUMGDURFUFUGZUHUSUI $.
  $}

  ${
    nvinv.1 $e |- X = ( BaseSet ` U ) $.
    nvinv.2 $e |- G = ( +v ` U ) $.
    nvinv.4 $e |- S = ( .sOLD ` U ) $.
    nvinv.5 $e |- M = ( inv ` G ) $.
    $( Minus 1 times a vector is the underlying group's inverse element.
       Equation 2 of [Kreyszig] p. 51.  (Contributed by NM, 15-Feb-2008.)
       (New usage is discouraged.) $)
    nvinv $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( -u 1 S A ) = ( M ` A ) ) $=
      ( cnv wcel c1st cfv cvc c1 cneg co wceq eqid nvvc vafval smfval vcm sylan
      bafval ) CKLCMNZOLAFLPQABRAENSCUGUGTUAABDEUGFCDHUBBCIUCCDFGHUFJUDUE $.
  $}

  ${
    $d x G $.  $d x N $.  $d x U $.
    nvinvfval.2 $e |- G = ( +v ` U ) $.
    nvinvfval.4 $e |- S = ( .sOLD ` U ) $.
    nvinvfval.3 $e |- N = ( S o. `' ( 2nd |` ( { -u 1 } X. _V ) ) ) $.
    $( Function for the negative of a vector on a normed complex vector space,
       in terms of the underlying addition group inverse.  (We currently do not
       have a separate notation for the negative of a vector.)  (Contributed by
       NM, 27-Mar-2008.)  (New usage is discouraged.) $)
    nvinvfval $p |- ( U e. NrmCVec -> N = ( inv ` G ) ) $=
      ( vx cnv wcel cba cfv cgn cc wf eqid neg1cn sylancl ffnd wfn c1 cneg nvsf
      cxp curry1f wf1o nvgrp bafval grpoinvf f1ofn 3syl cv wa co wceq curry1val
      cgr adantr nvinv eqtrd eqfnfvd ) BIJZHBKLZDCMLZVBVCVCDVBNVCUDZVCAOUAUBZNJ
      ZVCVCDOABVCVCPZFUCZQNVCVFVCADGUERSVBCUQJVCVCVDUFVDVCTBCEUGCVDVCBCVCVHEUHV
      DPZUIVCVCVDUJUKVBHULZVCJZUMZVKDLZVFVKAUNZVKVDLVMAVETZVGVNVOUOVBVPVLVBVEVC
      AVISURQNVCVFVKADGUPRVKABCVDVCVHEFVJUSUTVA $.
  $}

  ${
    nvm.1 $e |- X = ( BaseSet ` U ) $.
    nvm.2 $e |- G = ( +v ` U ) $.
    nvm.3 $e |- M = ( -v ` U ) $.
    nvm.6 $e |- N = ( /g ` G ) $.
    $( Vector subtraction in terms of group division operation.  (Contributed
       by NM, 15-Feb-2008.)  (New usage is discouraged.) $)
    nvm $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
          ( A M B ) = ( A N B ) ) $=
      ( co wceq cnv wcel w3a cgs cfv vsfval eqtr4i oveqi a1i ) ABELABFLMCNOAGOB
      GOPEFABEDQRFCDEIJSKTUAUB $.
  $}

  ${
    $d x y G $.  $d x y U $.  $d x y X $.
    nvmval.1 $e |- X = ( BaseSet ` U ) $.
    nvmval.2 $e |- G = ( +v ` U ) $.
    nvmval.4 $e |- S = ( .sOLD ` U ) $.
    nvmval.3 $e |- M = ( -v ` U ) $.
    $( Value of vector subtraction on a normed complex vector space.
       (Contributed by NM, 11-Sep-2007.)  (New usage is discouraged.) $)
    nvmval $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                ( A M B ) = ( A G ( -u 1 S B ) ) ) $=
      ( cnv wcel w3a cgs cfv co cgn wceq eqid cneg cgr nvgrp grpodivval syl3an1
      c1 bafval nvm nvinv 3adant2 oveq2d 3eqtr4d ) DLMZAGMZBGMZNZABEOPZQZABERPZ
      PZEQZABFQAUFUABCQZEQUMEUBMUNUOURVASDEIUCABUQEUSGDEGHIUGUSTZUQTZUDUEABDEFU
      QGHIKVDUHUPVBUTAEUMUOVBUTSUNBCDEUSGHIJVCUIUJUKUL $.

    $( Value of vector subtraction on a normed complex vector space.
       (Contributed by Mario Carneiro, 19-Nov-2013.)
       (New usage is discouraged.) $)
    nvmval2 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                ( A M B ) = ( ( -u 1 S B ) G A ) ) $=
      ( cnv wcel w3a co c1 cneg nvmval wceq cc neg1cn nvscl 3adant2 nvcom eqtrd
      mp3an2 syld3an3 ) DLMZAGMZBGMZNABFOAPQZBCOZEOZULAEOZABCDEFGHIJKRUHUIUJULG
      MZUMUNSUHUJUOUIUHUKTMUJUOUAUKBCDGHJUBUFUCAULDEGHIUDUGUE $.

    $( Value of the function for the vector subtraction operation on a normed
       complex vector space.  (Contributed by NM, 11-Sep-2007.)  (Revised by
       Mario Carneiro, 23-Dec-2013.)  (New usage is discouraged.) $)
    nvmfval $p |- ( U e. NrmCVec -> M = ( x e. X , y e. X |->
                    ( x G ( -u 1 S y ) ) ) ) $=
      ( cnv wcel cv cgn cfv co cmpo c1 wceq cgr nvgrp bafval vsfval grpodivfval
      cneg eqid syl w3a nvinv 3adant2 oveq2d mpoeq3dva eqtr4d ) DLMZFABGGANZBNZ
      EOPZPZEQZRZABGGUPSUFUQCQZEQZRUOEUAMFVATDEIUBABFEURGDEGHIUCURUGZDEFIKUDUEU
      HUOABGGVCUTUOUPGMZUQGMZUIVBUSUPEUOVFVBUSTVEUQCDEURGHIJVDUJUKULUMUN $.
  $}

  ${
    $d x y U $.  $d x y X $.
    nvmf.1 $e |- X = ( BaseSet ` U ) $.
    nvmf.3 $e |- M = ( -v ` U ) $.
    $( Mapping for the vector subtraction operation.  (Contributed by NM,
       11-Sep-2007.)  (Revised by Mario Carneiro, 23-Dec-2013.)
       (New usage is discouraged.) $)
    nvmf $p |- ( U e. NrmCVec -> M : ( X X. X ) --> X ) $=
      ( vx vy cnv wcel cxp wf cv c1 cneg cns cfv co wral wa eqid cpv cmpo simpl
      simprl cc neg1cn nvscl mp3an2 adantrl nvgcl syl3anc ralrimivva fmpo sylib
      nvmfval feq1d mpbird ) AHIZCCJZCBKUSCFGCCFLZMNZGLZAOPZQZAUAPZQZUBZKZURVFC
      IZGCRFCRVHURVIFGCCURUTCIZVBCIZSZSURVJVDCIZVIURVLUCURVJVKUDURVKVMVJURVAUEI
      VKVMUFVAVBVCACDVCTZUGUHUIUTVDAVECDVETZUJUKULFGCCVFCVGVGTUMUNURUSCBVGFGVCA
      VEBCDVOVNEUOUPUQ $.

    $( Closure law for the vector subtraction operation of a normed complex
       vector space.  (Contributed by NM, 11-Sep-2007.)
       (New usage is discouraged.) $)
    nvmcl $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A M B ) e. X ) $=
      ( cnv wcel cxp wf co nvmf fovcdm syl3an1 ) CHIEEJEDKAEIBEIABDLEICDEFGMABE
      EEDNO $.

    $( Cancellation law for vector subtraction.  ( ~ nnncan1 analog.)
       (Contributed by NM, 7-Mar-2008.)  (New usage is discouraged.) $)
    nvnnncan1 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
         ( ( A M B ) M ( A M C ) ) = ( C M B ) ) $=
      ( cnv wcel cpv cfv cablo w3a co wceq eqid nvablo bafval vsfval sylan
      ablonnncan1 ) DIJDKLZMJAFJBFJCFJNABEOACEOEOCBEOPDUCUCQZRABCEUCFDUCFGUDSDU
      CEUDHTUBUA $.
  $}

  ${
    nvmdi.1 $e |- X = ( BaseSet ` U ) $.
    nvmdi.3 $e |- M = ( -v ` U ) $.
    nvmdi.4 $e |- S = ( .sOLD ` U ) $.
    $( Distributive law for scalar product over subtraction.  (Contributed by
       NM, 14-Feb-2008.)  (New usage is discouraged.) $)
    nvmdi $p |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
       ( A S ( B M C ) ) = ( ( A S B ) M ( A S C ) ) ) $=
      ( cnv wcel cc w3a co wceq neg1cn nvscl oveq2d nvmval wa c1 cpv cfv simpr1
      cneg simpr2 mp3an2 3ad2antr3 3jca eqid nvdi syldan mp3anr2 3adantr2 eqtrd
      nvscom 3adant3r1 simpl 3adant3r3 3adant3r2 syl3anc 3eqtr4d ) EKLZAMLZBGLZ
      CGLZNZUAZABUBUFZCDOZEUCUDZOZDOZABDOZVJACDOZDOZVLOZABCFOZDOVOVPFOZVIVNVOAV
      KDOZVLOZVRVDVHVEVFVKGLZNVNWBPVIVEVFWCVDVEVFVGUEVDVEVFVGUGVDVEVGWCVFVDVJML
      ZVGWCQVJCDEGHJRUHUIUJABVKDEVLGHVLUKZJULUMVIWAVQVOVLVDVEVGWAVQPZVFVDVEWDVG
      WFQAVJCDEGHJUQUNUOSUPVIVSVMADVDVFVGVSVMPVEBCDEVLFGHWEJITURSVIVDVOGLZVPGLZ
      VTVRPVDVHUSVDVEVFWGVGABDEGHJRUTVDVEVGWHVFACDEGHJRVAVOVPDEVLFGHWEJITVBVC
      $.
  $}

  ${
    nvnegneg.1 $e |- X = ( BaseSet ` U ) $.
    nvnegneg.4 $e |- S = ( .sOLD ` U ) $.
    $( Double negative of a vector.  (Contributed by NM, 4-Dec-2007.)
       (New usage is discouraged.) $)
    nvnegneg $p |- ( ( U e. NrmCVec /\ A e. X ) ->
                  ( -u 1 S ( -u 1 S A ) ) = A ) $=
      ( cnv wcel wa c1 cneg co cpv cfv cgn wceq cc neg1cn eqid nvinv mp3an2 cgr
      nvscl syldan fveq2d nvgrp bafval grpo2inv sylan 3eqtrd ) CGHZADHZIZJKZUNA
      BLZBLZUOCMNZONZNZAURNZURNZAUKULUODHZUPUSPUKUNQHULVBRUNABCDEFUCUAUOBCUQURD
      EUQSZFURSZTUDUMUOUTURABCUQURDEVCFVDTUEUKUQUBHULVAAPCUQVCUFAUQURDCUQDEVCUG
      VDUHUIUJ $.
  $}

  ${
    nvmul0or.1 $e |- X = ( BaseSet ` U ) $.
    nvmul0or.4 $e |- S = ( .sOLD ` U ) $.
    nvmul0or.6 $e |- Z = ( 0vec ` U ) $.
    $( If a scalar product is zero, one of its factors must be zero.
       (Contributed by NM, 6-Dec-2007.)  (New usage is discouraged.) $)
    nvmul0or $p |- ( ( U e. NrmCVec /\ A e. CC /\ B e. X ) ->
                    ( ( A S B ) = Z <-> ( A = 0 \/ B = Z ) ) ) $=
      ( wcel cc co wceq cc0 wa c1 oveq2 3ad2antl2 3adant2 3eqtr3d cnv w3a wo wn
      wne df-ne cdiv ad2antlr recid2 oveq1d simpl1 reccl simpl2 simpl3 syl13anc
      cmul nvsass adantr adantlr nvsz sylan2 anassrs 3adantl3 ex biimtrrid orrd
      nvsid wi nv0 oveq1 eqeq1d syl5ibrcom 3adant3 jaod impbid ) DUAJZAKJZBEJZU
      BZABCLZFMZANMZBFMZUCZVSWAWDVSWAOZWBWCWBUDANUEZWEWCANUFWEWFWCWEWFOPAUGLZVT
      CLZWGFCLZBFWAWHWIMVSWFVTFWGCQUHVSWFWHBMWAVSWFOZWGAUPLZBCLZPBCLZWHBVQVPWFW
      LWMMVRVQWFOZWKPBCAUIUJRWJVPWGKJZVQVRWLWHMVPVQVRWFUKVQVPWFWOVRAULZRVPVQVRW
      FUMVPVQVRWFUNWGABCDEGHUQUOVSWMBMZWFVPVRWQVQBCDEGHVGSURTUSVSWFWIFMZWAVPVQW
      FWRVRVPVQWFWRWNVPWOWRWPWGCDFHIUTVAVBVCUSTVDVEVFVDVSWBWAWCVPVRWBWAVHVQVPVR
      OWAWBNBCLZFMBCDEFGHIVIWBVTWSFANBCVJVKVLSVPVQWCWAVHVRVPVQOWAWCAFCLZFMACDFH
      IUTWCVTWTFBFACQVKVLVMVNVO $.
  $}

  ${
    nvrinv.1 $e |- X = ( BaseSet ` U ) $.
    nvrinv.2 $e |- G = ( +v ` U ) $.
    nvrinv.4 $e |- S = ( .sOLD ` U ) $.
    nvrinv.6 $e |- Z = ( 0vec ` U ) $.
    $( A vector minus itself.  (Contributed by NM, 4-Dec-2007.)  (Revised by
       Mario Carneiro, 21-Dec-2013.)  (New usage is discouraged.) $)
    nvrinv $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( A G ( -u 1 S A ) ) = Z ) $=
      ( cnv wcel wa cgn cfv co cgi c1 wceq eqid cgr nvgrp bafval grporinv sylan
      cneg nvinv oveq2d 0vfval adantr 3eqtr4d ) CKLZAELZMZAADNOZOZDPZDQOZARUFAB
      PZDPFULDUALUMUQURSCDHUBAURDUOECDEGHUCURTUOTZUDUEUNUSUPADABCDUOEGHIUTUGUHU
      LFURSUMCDKFHJUIUJUK $.

    $( Minus a vector plus itself.  (Contributed by NM, 4-Dec-2007.)  (Revised
       by Mario Carneiro, 21-Dec-2013.)  (New usage is discouraged.) $)
    nvlinv $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( ( -u 1 S A ) G A ) = Z ) $=
      ( cnv wcel wa cgn cfv co cgi c1 wceq eqid cgr nvgrp bafval grpolinv sylan
      cneg nvinv oveq1d 0vfval adantr 3eqtr4d ) CKLZAELZMZADNOZOZADPZDQOZRUFABP
      ZADPFULDUALUMUQURSCDHUBAURDUOECDEGHUCURTUOTZUDUEUNUSUPADABCDUOEGHIUTUGUHU
      LFURSUMCDKFHJUIUJUK $.
  $}

  ${
    nvpncan2.1 $e |- X = ( BaseSet ` U ) $.
    nvpncan2.2 $e |- G = ( +v ` U ) $.
    nvpncan2.3 $e |- M = ( -v ` U ) $.
    $( Cancellation law for vector subtraction.  (Contributed by NM,
       27-Dec-2007.)  (New usage is discouraged.) $)
    nvpncan2 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                 ( ( A G B ) M A ) = B ) $=
      ( cnv wcel w3a co c1 cneg cfv wceq eqid 3adant3 eqtrd simp1 nvgcl syl3anc
      cns simp2 nvmval simp3 neg1cn nvscl mp3an2 nvadd32 syl13anc nvrinv oveq1d
      cc cn0v nv0lid 3adant2 ) CJKZAFKZBFKZLZABDMZAEMZVCNOZACUDPZMZDMZBVBUSVCFK
      UTVDVHQUSUTVAUAZABCDFGHUBUSUTVAUEZVCAVFCDEFGHVFRZIUFUCVBVHAVGDMZBDMZBVBUS
      UTVAVGFKZVHVMQVIVJUSUTVAUGUSUTVNVAUSVEUOKUTVNUHVEAVFCFGVKUIUJSABVGCDFGHUK
      ULVBVMCUPPZBDMZBVBVLVOBDUSUTVLVOQVAAVFCDFVOGHVKVORZUMSUNUSVAVPBQUTBCDFVOG
      HVQUQURTTT $.

    $( Cancellation law for vector subtraction.  (Contributed by NM,
       24-Jan-2008.)  (New usage is discouraged.) $)
    nvpncan $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                 ( ( A G B ) M B ) = A ) $=
      ( cnv wcel co wceq w3a nvcom oveq1d nvpncan2 eqtr3d 3com23 ) CJKZBFKZAFKZ
      ABDLZBELZAMTUAUBNZBADLZBELUDAUEUFUCBEBACDFGHOPBACDEFGHIQRS $.

    $( Commutative/associative law for vector addition and subtraction.
       (Contributed by NM, 24-Jan-2008.)  (New usage is discouraged.) $)
    nvaddsub $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
      ( ( A G B ) M C ) = ( ( A M C ) G B ) ) $=
      ( cnv wcel cablo w3a co wceq nvablo bafval vsfval ablomuldiv sylan ) DKLE
      MLAGLBGLCGLNABEOCFOACFOBEOPDEIQABCFEGDEGHIRDEFIJSTUA $.

    $( Cancellation law for a normed complex vector space.  (Contributed by NM,
       24-Jan-2008.)  (New usage is discouraged.) $)
    nvnpcan $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
         ( ( A M B ) G B ) = A ) $=
      ( cnv wcel w3a co wceq wa simprl simprr 3jca nvaddsub syldan 3impb eqtr3d
      nvpncan ) CJKZAFKZBFKZLABDMBEMZABEMBDMZAUDUEUFUGUHNZUDUEUFOZUEUFUFLUIUDUJ
      OUEUFUFUDUEUFPUDUEUFQZUKRABBCDEFGHISTUAABCDEFGHIUCUB $.

    $( Rearrangement of 4 terms in a mixed vector addition and subtraction.
       (Contributed by NM, 8-Feb-2008.)  (New usage is discouraged.) $)
    nvaddsub4 $p |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X ) /\ ( C e. X /\
       D e. X ) ) -> ( ( A G B ) M ( C G D ) ) = ( ( A M C ) G ( B M D ) ) ) $=
      ( wcel wa co wceq neg1cn 3adant2 nvscl mp3an2 nvmval cnv w3a cneg cns cfv
      c1 cc eqid nvdi mp3anr1 oveq2d anim12dan syld3an3 eqtrd simp1 nvgcl 3expb
      3adant3 syl3anc 3adant3r 3adant2r 3adant3l 3adant2l oveq12d 3eqtr4d
      nvadd4 ) EUALZAHLZBHLZMZCHLZDHLZMZUBZABFNZUFUCZCDFNZEUDUEZNZFNZAVPCVRNZFN
      ZBVPDVRNZFNZFNZVOVQGNZACGNZBDGNZFNVNVTVOWAWCFNZFNZWEVNVSWIVOFVGVMVSWIOZVJ
      VGVPUGLZVKVLWKPVPCDVREFHIJVRUHZUIUJQUKVGVJVMWAHLZWCHLZMZWJWEOVGVMWPVJVGVK
      WNVLWOVGWLVKWNPVPCVREHIWMRSVGWLVLWOPVPDVREHIWMRSULQABWAWCEFHIJVFUMUNVNVGV
      OHLZVQHLZWFVTOVGVJVMUOVGVJWQVMVGVHVIWQABEFHIJUPUQURVGVMWRVJVGVKVLWRCDEFHI
      JUPUQQVOVQVREFGHIJWMKTUSVNWGWBWHWDFVGVHVMWGWBOZVIVGVHVKWSVLACVREFGHIJWMKT
      UTVAVGVIVMWHWDOZVHVGVIVLWTVKBDVREFGHIJWMKTVBVCVDVE $.
  $}

  ${
    nvmeq0.1 $e |- X = ( BaseSet ` U ) $.
    nvmeq0.3 $e |- M = ( -v ` U ) $.
    nvmeq0.5 $e |- Z = ( 0vec ` U ) $.
    $( The difference between two vectors is zero iff they are equal.
       (Contributed by NM, 24-Jan-2008.)  (New usage is discouraged.) $)
    nvmeq0 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
            ( ( A M B ) = Z <-> A = B ) ) $=
      ( cnv wcel w3a co cpv cfv wceq wb wa nvmcl 3expb nvzcl adantr simprr 3jca
      eqid nvrcan syldan 3impb nvnpcan nv0lid 3adant2 eqeq12d bitr3d ) CJKZAEKZ
      BEKZLZABDMZBCNOZMZFBUSMZPZURFPZABPUNUOUPVBVCQZUNUOUPRZUREKZFEKZUPLVDUNVER
      VFVGUPUNUOUPVFABCDEGHSTUNVGVECEFGIUAUBUNUOUPUCUDURFBCUSEGUSUEZUFUGUHUQUTA
      VABABCUSDEGVHHUIUNUPVABPUOBCUSEFGVHIUJUKULUM $.

    $( A vector minus itself is the zero vector.  (Contributed by NM,
       28-Jan-2008.)  (New usage is discouraged.) $)
    nvmid $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( A M A ) = Z ) $=
      ( cnv wcel wa co wceq eqid wb nvmeq0 3anidm23 mpbiri ) BIJZADJZKAACLEMZAA
      MZANSTUAUBOAABCDEFGHPQR $.
  $}

  ${
    $d x y N $.  $d x y U $.  $d x y X $.
    nvf.1 $e |- X = ( BaseSet ` U ) $.
    nvf.6 $e |- N = ( normCV ` U ) $.
    $( Mapping for the norm function.  (Contributed by NM, 11-Nov-2006.)
       (New usage is discouraged.) $)
    nvf $p |- ( U e. NrmCVec -> N : X --> RR ) $=
      ( vx vy cnv wcel cpv cfv cns cop cvc cr cv wceq co wral eqid wf cn0v cabs
      cc0 wi cmul cc caddc cle wbr w3a nvi simp2d ) AHIAJKZALKZMNICOBUAFPZBKZUD
      QUPAUBKZQUEGPZUPUORBKUSUCKUQUFRQGUGSUPUSUNRBKUQUSBKUHRUIUJGCSUKFCSFGUOAUN
      BCURDUNTUOTURTEULUM $.

    $( The norm of a normed complex vector space is a real number.
       (Contributed by NM, 24-Nov-2006.)  (New usage is discouraged.) $)
    nvcl $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( N ` A ) e. RR ) $=
      ( cnv wcel cr nvf ffvelcdmda ) BGHDIACBCDEFJK $.

    ${
      nvcli.9 $e |- U e. NrmCVec $.
      nvcli.7 $e |- A e. X $.
      $( The norm of a normed complex vector space is a real number.
         (Contributed by NM, 20-Apr-2007.)  (New usage is discouraged.) $)
      nvcli $p |- ( N ` A ) e. RR $=
        ( cnv wcel cfv cr nvcl mp2an ) BIJADJACKLJGHABCDEFMN $.
    $}
  $}

  ${
    $d y A $.  $d x y B $.  $d x y N $.  $d x y S $.  $d x y U $.  $d x y X $.
    nvs.1 $e |- X = ( BaseSet ` U ) $.
    nvs.4 $e |- S = ( .sOLD ` U ) $.
    nvs.6 $e |- N = ( normCV ` U ) $.
    $( Proportionality property of the norm of a scalar product in a normed
       complex vector space.  (Contributed by NM, 11-Nov-2006.)
       (New usage is discouraged.) $)
    nvs $p |- ( ( U e. NrmCVec /\ A e. CC /\ B e. X ) ->
               ( N ` ( A S B ) ) = ( ( abs ` A ) x. ( N ` B ) ) ) $=
      ( vy vx wcel cc co cfv cabs cmul wceq cv wral cnv wa cc0 wi cpv caddc cle
      cn0v wbr w3a cop cvc cr wf nvi simp3d simp2 ralimi syl oveq2 fveq2d fveq2
      eqid oveq2d eqeq12d fvoveq1 oveq1d rspc2v syl5 3impia 3com13 ) BFLZAMLZDU
      ALZABCNEOZAPOZBEOZQNZRZVLVMVNVSVNJSZKSZCNZEOZVTPOZWAEOZQNZRZJMTZKFTZVLVMU
      BVSVNWEUCRWADUHOZRUDZWHWAVTDUEOZNEOWEVTEOUFNUGUIJFTZUJZKFTZWIVNWLCUKULLFU
      MEUNWOKJCDWLEFWJGWLVCHWJVCIUOUPWNWHKFWKWHWMUQURUSWGVSVTBCNZEOZWDVQQNZRKJB
      AFMWABRZWCWQWFWRWSWBWPEWABVTCUTVAWSWEVQWDQWABEVBVDVEVTARZWQVOWRVRVTABECVF
      WTWDVPVQQVTAPVBVGVEVHVIVJVK $.

    $( The norm of a scalar product with a nonnegative real.  (Contributed by
       NM, 1-Jan-2008.)  (New usage is discouraged.) $)
    nvsge0 $p |- ( ( U e. NrmCVec /\ ( A e. RR /\ 0 <_ A ) /\ B e. X ) ->
               ( N ` ( A S B ) ) = ( A x. ( N ` B ) ) ) $=
      ( cnv wcel cr cc0 cle wbr wa co cfv cmul wceq w3a cabs cc recn adantr nvs
      syl3an2 absid 3ad2ant2 oveq1d eqtrd ) DJKZALKZMANOZPZBFKZUAZABCQERZAUBRZB
      ERZSQZAUTSQUOULAUCKZUPURVATUMVBUNAUDUEABCDEFGHIUFUGUQUSAUTSUOULUSATUPAUHU
      IUJUK $.

    $( The norm of the negative of a vector.  (Contributed by NM, 28-Nov-2006.)
       (New usage is discouraged.) $)
    nvm1 $p |- ( ( U e. NrmCVec /\ A e. X ) ->
               ( N ` ( -u 1 S A ) ) = ( N ` A ) ) $=
      ( cnv wcel wa c1 cneg co cfv cabs cmul cc wceq neg1cn mp3an2 absnegi abs1
      nvs ax-1cn eqtri oveq1i nvcl recnd mullidd eqtrid eqtrd ) CIJZAEJZKZLMZAB
      NDOZUPPOZADOZQNZUSUMUPRJUNUQUTSTUPABCDEFGHUDUAUOUTLUSQNUSURLUSQURLPOLLUEU
      BUCUFUGUOUSUOUSACDEFHUHUIUJUKUL $.
  $}

  ${
    nvdif.1 $e |- X = ( BaseSet ` U ) $.
    nvdif.2 $e |- G = ( +v ` U ) $.
    nvdif.4 $e |- S = ( .sOLD ` U ) $.
    nvdif.6 $e |- N = ( normCV ` U ) $.
    $( The norm of the difference between two vectors.  (Contributed by NM,
       1-Dec-2006.)  (New usage is discouraged.) $)
    nvdif $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
               ( N ` ( A G ( -u 1 S B ) ) ) = ( N ` ( B G ( -u 1 S A ) ) ) ) $=
      ( wcel co cfv wceq neg1cn nvscl mp3an2 3adant3 syl3anc cnv w3a c1 cneg cc
      simp1 a1i simp3 nvdi syl13anc nvnegneg oveq2d 3adant2 simp2 3eqtrd fveq2d
      nvcom nvgcl nvm1 syl2anc eqtr3d ) DUALZAGLZBGLZUBZUCUDZBVFACMZEMZCMZFNZAV
      FBCMZEMZFNVHFNZVEVIVLFVEVIVKVFVGCMZEMZVKAEMZVLVEVBVFUELZVDVGGLZVIVOOVBVCV
      DUFZVQVEPUGVBVCVDUHZVBVCVRVDVBVQVCVRPVFACDGHJQRSZVFBVGCDEGHIJUIUJVEVNAVKE
      VBVCVNAOVDACDGHJUKSULVEVBVKGLZVCVPVLOVSVBVDWBVCVBVQVDWBPVFBCDGHJQRUMVBVCV
      DUNVKADEGHIUQTUOUPVEVBVHGLZVJVMOVSVEVBVDVRWCVSVTWABVGDEGHIURTVHCDFGHJKUSU
      TVA $.

    $( The norm of a vector plus the imaginary scalar product of another.
       (Contributed by NM, 2-Feb-2007.)  (New usage is discouraged.) $)
    nvpi $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
               ( N ` ( A G ( _i S B ) ) ) = ( N ` ( B G ( -u _i S A ) ) ) ) $=
      ( wcel c1 ci co cfv cmul cneg ax-icn wceq cnv w3a cr simp1 mp3an2 3adant2
      nvscl nvgcl syld3an3 nvcl syl2anc recnd mullidd cabs absnegi eqtri oveq1i
      absi negicn nvs simp2 nvdi mp3anr1 syl12anc mulneg1i ixi negeqi negneg1e1
      cc nvsass mpanr1 nvsid 3eqtr3a oveq2d nvcom syld3an2 3eqtrd fveq2d eqtr3d
      wa 3adant3 eqtr3id ) DUALZAGLZBGLZUBZMANBCOZEOZFPZQOZWIBNRZACOZEOZFPZWFWI
      WFWIWFWCWHGLZWIUCLWCWDWEUDZWCWDWEWGGLZWOWCWEWQWDWCNVILZWEWQSNBCDGHJUGUEUF
      ZAWGDEGHIUHUIZWHDFGHKUJUKULUMWFWJWKUNPZWIQOZWNXAMWIQXANUNPMNSUOURUPUQWFWK
      WHCOZFPZXBWNWFWCWOXDXBTZWPWTWCWKVILZWOXEUSWKWHCDFGHJKUTUEUKWFXCWMFWFXCWLW
      KWGCOZEOZWLBEOZWMWFWCWDWQXCXHTZWPWCWDWEVAWSWCXFWDWQXJUSWKAWGCDEGHIJVBVCVD
      WFXGBWLEWCWEXGBTWDWCWEVTWKNQOZBCOZMBCOXGBXKMBCXKNNQOZRZMNNSSVEXNMRZRMXMXO
      VFVGVHUPUPUQWCWRWEXLXGTZSWCXFWRWEXPUSWKNBCDGHJVJVCVKBCDGHJVLVMUFVNWCWLGLZ
      WDWEXIWMTWCWDXQWEWCXFWDXQUSWKACDGHJUGUEWAWLBDEGHIVOVPVQVRVSWBVS $.
  $}

  ${
    nvz0.5 $e |- Z = ( 0vec ` U ) $.
    nvz0.6 $e |- N = ( normCV ` U ) $.
    $( The norm of a zero vector is zero.  (Contributed by NM, 24-Nov-2006.)
       (New usage is discouraged.) $)
    nvz0 $p |- ( U e. NrmCVec -> ( N ` Z ) = 0 ) $=
      ( cnv wcel cc0 cns cfv co cmul cba wceq eqid nvzcl cr cle wa mpdan pm3.2i
      wbr 0re 0le0 nvsge0 mp3an2 nv0 fveq2d cc nvcl recnd mul02d 3eqtr3d ) AFGZ
      HCAIJZKZBJZHCBJZLKZURHUNCAMJZGZUQUSNZAUTCUTOZDPZUNHQGZHHRUBZSVAVBVEVFUCUD
      UAHCUOABUTVCUOOZEUEUFTUNUPCBUNVAUPCNVDCUOAUTCVCVGDUGTUHUNURUNVAURUIGVDUNV
      ASURCABUTVCEUJUKTULUM $.
  $}

  ${
    $d x A $.  $d x y N $.  $d x y U $.  $d x y X $.  $d x Z $.
    nvz.1 $e |- X = ( BaseSet ` U ) $.
    nvz.5 $e |- Z = ( 0vec ` U ) $.
    nvz.6 $e |- N = ( normCV ` U ) $.
    $( The norm of a vector is zero iff the vector is zero.  First part of
       Problem 2 of [Kreyszig] p. 64.  (Contributed by NM, 24-Nov-2006.)
       (New usage is discouraged.) $)
    nvz $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( ( N ` A ) = 0 <-> A = Z ) ) $=
      ( vx vy cnv wcel cfv cc0 wceq wi cv co wral eqid wa cns cabs cc cpv caddc
      cmul cle wbr w3a cop cvc cr nvi simp3d simp1 ralimi fveqeq2 eqeq1 imbi12d
      wf rspccv 3syl imp fveq2 nvz0 sylan9eqr ex adantr impbid ) BKLZADLZUAACMZ
      NOZAEOZVKVLVNVOPZVKIQZCMZNOZVQEOZPZJQZVQBUBMZRCMWBUCMVRUGROJUDSZVQWBBUEMZ
      RCMVRWBCMUFRUHUIJDSZUJZIDSZWAIDSVLVPPVKWEWCUKULLDUMCVAWHIJWCBWECDEFWETWCT
      GHUNUOWGWAIDWAWDWFUPUQWAVPIADVQAOVSVNVTVOVQANCURVQAEUSUTVBVCVDVKVOVNPVLVK
      VOVNVOVKVMECMNAECVEBCEGHVFVGVHVIVJ $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y G $.  $d x y N $.  $d x y U $.  $d x y X $.
    nvtri.1 $e |- X = ( BaseSet ` U ) $.
    nvtri.2 $e |- G = ( +v ` U ) $.
    nvtri.6 $e |- N = ( normCV ` U ) $.
    $( Triangle inequality for the norm of a normed complex vector space.
       (Contributed by NM, 11-Nov-2006.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.) $)
    nvtri $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
          ( N ` ( A G B ) ) <_ ( ( N ` A ) + ( N ` B ) ) ) $=
      ( vx vy wcel co cfv caddc cle wbr cv wral wceq cnv wa cn0v c1st c2nd cabs
      cc0 wi cmul cc w3a cop cvc cr wf cns eqid smfval eqcomi nvi simp3d ralimi
      simp3 fvoveq1 fveq2 oveq1d breq12d oveq2 fveq2d oveq2d rspc2v syl5 3impia
      syl 3comr ) AFLZBFLZCUALZABDMZENZAENZBENZOMZPQZVPVQVRWDVRJRZKRZDMENZWEENZ
      WFENZOMZPQZKFSZJFSZVPVQUBWDVRWHUGTWECUCNZTUHZWFWECUDNUENZMENWFUFNWHUIMTKU
      JSZWLUKZJFSZWMVRDWPULUMLFUNEUOWSJKWPCDEFWNGHCUPNZWPWTCWTUQURUSWNUQIUTVAWR
      WLJFWOWQWLVCVBVNWKWDAWFDMZENZWAWIOMZPQJKABFFWEATZWGXBWJXCPWEAWFEDVDXDWHWA
      WIOWEAEVEVFVGWFBTZXBVTXCWCPXEXAVSEWFBADVHVIXEWIWBWAOWFBEVEVJVGVKVLVMVO $.
  $}

  ${
    nvmtri.1 $e |- X = ( BaseSet ` U ) $.
    nvmtri.3 $e |- M = ( -v ` U ) $.
    nvmtri.6 $e |- N = ( normCV ` U ) $.
    $( Triangle inequality for the norm of a vector difference.  (Contributed
       by NM, 27-Dec-2007.)  (New usage is discouraged.) $)
    nvmtri $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
          ( N ` ( A M B ) ) <_ ( ( N ` A ) + ( N ` B ) ) ) $=
      ( wcel c1 cfv co caddc cle neg1cn eqid mp3an2 3adant2 cmul cnv w3a cns cc
      cneg cpv wbr nvscl syld3an3 nvmval fveq2d wceq wa cabs nvs ax-1cn absnegi
      nvtri abs1 eqtri oveq1i nvcl recnd mullidd eqtrid eqtr2d oveq2d 3brtr4d )
      CUAJZAFJZBFJZUBZAKUEZBCUCLZMZCUFLZMZELZAELZVOELZNMZABDMZELVSBELZNMOVIVJVK
      VOFJZVRWAOUGVIVKWDVJVIVMUDJZVKWDPVMBVNCFGVNQZUHRSAVOCVPEFGVPQZIURUIVLWBVQ
      EABVNCVPDFGWGWFHUJUKVLWCVTVSNVIVKWCVTULVJVIVKUMZVTVMUNLZWCTMZWCVIWEVKVTWJ
      ULPVMBVNCEFGWFIUORWHWJKWCTMWCWIKWCTWIKUNLKKUPUQUSUTVAWHWCWHWCBCEFGIVBVCVD
      VEVFSVGVH $.
  $}

  ${
    nvabs.1 $e |- X = ( BaseSet ` U ) $.
    nvabs.2 $e |- G = ( +v ` U ) $.
    nvabs.4 $e |- S = ( .sOLD ` U ) $.
    nvabs.6 $e |- N = ( normCV ` U ) $.
    $( Norm difference property of a normed complex vector space.  Problem 3 of
       [Kreyszig] p. 64.  (Contributed by NM, 4-Dec-2006.)
       (New usage is discouraged.) $)
    nvabs $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
       ( abs ` ( ( N ` A ) - ( N ` B ) ) ) <_ ( N ` ( A G ( -u 1 S B ) ) ) ) $=
      ( wcel cfv co cle wbr cr nvcl 3adant2 wceq cnv w3a cmin cabs nvdif negeqd
      c1 cneg 3adant3 simp1 neg1cn nvscl mp3an2 nvgcl syld3an3 syl2anc renegcld
      cc 3com23 caddc nvcom cn0v wa simprr adantrr simprl 3jca nvass 3impb eqid
      syldan nvlinv oveq2d nv0rid 3eqtrd eqtrd fveq2d eqbrtrrd subnegd breqtrrd
      nvtri recnd lesubd eqbrtrd simp2 simp3 syl13anc syld3an2 lesubaddd mpbird
      resubcld absled mpbir2and ) DUALZAGLZBGLZUBZAFMZBFMZUCNZUDMAUGUHZBCNZENZF
      MZOPXDUHZWTOPWTXDOPZWQXEBXAACNZENZFMZUHZWTOWQXDXIABCDEFGHIJKUEUFWQWSWRXJW
      NWPWSQLWOBDFGHKRSZWNWOWRQLWPADFGHKRUIZWQXIWQWNXHGLZXIQLWNWOWPUJZWNWPWOXMW
      NWPWOXGGLZXMWNWOXOWPWNXAURLZWOXOUKXAACDGHJULUMZSBXGDEGHIUNUOUSZXHDFGHKRUP
      ZUQWQWSWRXIUTNZWRXJUCNOWQAXHENZFMZWSXTOWQYABFWQYAXHAENZBWNWOWPXMYAYCTXRAX
      HDEGHIVAUOWQYCBXGAENZENZBDVBMZENZBWNWOWPYCYETZWNWOWPVCZWPXOWOUBYHWNYIVCWP
      XOWOWNWOWPVDWNWOXOWPXQVEWNWOWPVFVGBXGADEGHIVHVKVIWQYDYFBEWNWOYDYFTWPACDEG
      YFHIJYFVJZVLUIVMWNWPYGBTWOBDEGYFHIYJVNSVOVPVQWNWOWPXMYBXTOPXRAXHDEFGHIKWA
      UOVRWQWRXIWQWRXLWBWQXIXSWBVSVTWCWDWQXFWRXDWSUTNZOPWQXCBENZFMZWRYKOWQYLAFW
      QYLAXBBENZENZAYFENZAWQWNWOXBGLZWPYLYOTXNWNWOWPWEWNWPYQWOWNXPWPYQUKXABCDGH
      JULUMSZWNWOWPWFAXBBDEGHIVHWGWQYNYFAEWNWPYNYFTWOBCDEGYFHIJYJVLSVMWNWOYPATW
      PADEGYFHIYJVNUIVOVQWNXCGLZWOWPYMYKOPWNWOWPYQYSYRAXBDEGHIUNUOZXCBDEFGHIKWA
      WHVRWQWRWSXDXLXKWQWNYSXDQLXNYTXCDFGHKRUPZWIWJWQWTXDWQWRWSXLXKWKUUAWLWM $.
  $}

  ${
    nvge0.1 $e |- X = ( BaseSet ` U ) $.
    nvge0.6 $e |- N = ( normCV ` U ) $.
    $( The norm of a normed complex vector space is nonnegative.  Second part
       of Problem 2 of [Kreyszig] p. 64.  (Contributed by NM, 28-Nov-2006.)
       (Proof shortened by AV, 10-Jul-2022.)  (New usage is discouraged.) $)
    nvge0 $p |- ( ( U e. NrmCVec /\ A e. X ) -> 0 <_ ( N ` A ) ) $=
      ( cnv wcel wa c2 cfv cc0 c1 co caddc cle wceq eqid cc neg1cn crp 2rp nvcl
      a1i cneg cns cmul cpv cn0v nvz0 adantr 1pneg1e0 oveq1i nv0 eqtr2id ax-1cn
      nvdir mp3anr1 mpanr1 nvsid oveq1d 3eqtrd fveq2d eqtr3d nvscl mp3an2 nvtri
      wbr mpd3an3 eqbrtrd nvm1 oveq2d recnd 2timesd eqtr4d breqtrd prodge0rd )
      BGHZADHZIZJACKZJUAHVTUBUDABCDEFUCZVTLWAMUEZABUFKZNZCKZONZJWAUGNZPVTLAWEBU
      HKZNZCKZWGPVTBUIKZCKZLWKVRWMLQVSBCWLWLRZFUJUKVTWLWJCVTWLMWCONZAWDNZMAWDNZ
      WEWINZWJVTWPLAWDNWLWOLAWDULUMAWDBDWLEWDRZWNUNUOVRWCSHZVSWPWRQZTVRMSHWTVSX
      AUPMWCAWDBWIDEWIRZWSUQURUSVTWQAWEWIAWDBDEWSUTVAVBVCVDVRVSWEDHZWKWGPVHVRWT
      VSXCTWCAWDBDEWSVEVFAWEBWICDEXBFVGVIVJVTWGWAWAONWHVTWFWAWAOAWDBCDEWSFVKVLV
      TWAVTWAWBVMVNVOVPVQ $.
  $}

  ${
    nvgt0.1 $e |- X = ( BaseSet ` U ) $.
    nvgt0.5 $e |- Z = ( 0vec ` U ) $.
    nvgt0.6 $e |- N = ( normCV ` U ) $.
    $( A nonzero norm is positive.  (Contributed by NM, 20-Nov-2007.)
       (New usage is discouraged.) $)
    nvgt0 $p |- ( ( U e. NrmCVec /\ A e. X ) ->
                   ( A =/= Z <-> 0 < ( N ` A ) ) ) $=
      ( cnv wcel wa cfv cc0 wne clt wbr nvz necon3bid cr cle nvcl nvge0 syl2anc
      wb ne0gt0 bitr3d ) BIJADJKZACLZMNZAENMUHOPZUGUHMAEABCDEFGHQRUGUHSJMUHTPUI
      UJUDABCDFHUAABCDFHUBUHUEUCUF $.
  $}

  ${
    nv1.1 $e |- X = ( BaseSet ` U ) $.
    nv1.4 $e |- S = ( .sOLD ` U ) $.
    nv1.5 $e |- Z = ( 0vec ` U ) $.
    nv1.6 $e |- N = ( normCV ` U ) $.
    $( From any nonzero vector, construct a vector whose norm is one.
       (Contributed by NM, 6-Dec-2007.)  (New usage is discouraged.) $)
    nv1 $p |- ( ( U e. NrmCVec /\ A e. X /\ A =/= Z ) ->
               ( N ` ( ( 1 / ( N ` A ) ) S A ) ) = 1 ) $=
      ( wcel wne c1 cfv co cr cc0 cle wbr 3adant3 cnv cdiv cmul wceq simp1 nvcl
      w3a wa nvz necon3bid biimp3ar rereccld clt nvgt0 biimp3a 1re 0le1 mpanl12
      divge0 syl2anc simp2 nvsge0 syl121anc cc recnd recid2d eqtrd ) CUAKZAEKZA
      FLZUGZMADNZUBOZABODNZVMVLUCOZMVKVHVMPKQVMRSZVIVNVOUDVHVIVJUEVKVLVHVIVLPKZ
      VJACDEGJUFZTZVHVIVLQLVJVHVIUHZVLQAFACDEFGIJUIUJUKZULVKVQQVLUMSZVPVSVHVIVJ
      WBACDEFGIJUNUOMPKQMRSVQWBUHVPUPUQMVLUSURUTVHVIVJVAVMABCDEGHJVBVCVKVLVHVIV
      LVDKVJVTVLVRVETWAVFVG $.
  $}

  ${
    nvop.2 $e |- G = ( +v ` U ) $.
    nvop.4 $e |- S = ( .sOLD ` U ) $.
    nvop.6 $e |- N = ( normCV ` U ) $.
    $( A complex inner product space in terms of ordered pair components.
       (Contributed by NM, 11-Sep-2007.)  (New usage is discouraged.) $)
    nvop $p |- ( U e. NrmCVec -> U = <. <. G , S >. , N >. ) $=
      ( cnv wcel c1st cfv c2nd cop wrel wceq nvrel 1st2nd mpan nmcvfval opeq2i
      eqid nvvop opeq1d eqtr3id eqtrd ) BHIZBBJKZBLKZMZCAMZDMZHNUFBUIOPBHQRUFUI
      UGDMUKDUHUGBDGSTUFUGUJDABCUGUGUAEFUBUCUDUE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples of normed complex vector spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    cnnv.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The set of complex numbers is a normed complex vector space.  The vector
       operation is ` + ` , the scalar product is ` x. ` , and the norm
       function is ` abs ` .  (Contributed by Steve Rodriguez, 3-Dec-2006.)
       (New usage is discouraged.) $)
    cnnv $p |- U e. NrmCVec $=
      ( vx vy cmul caddc cabs cc cc0 cablo wcel cgr cnaddabloOLD ablogrpo ax-mp
      cxp ax-addf fdmi cv wceq grporn cnidOLD cncvcOLD absf abs00 biimpa absmul
      cfv abstri isnvi ) CDEAFGHIFHFJKFLKMFNOHHPHFQRUAUBUCUDCSZHKUKGUHITUKITUKU
      EUFDSZUKUGUKULUIBUJ $.
  $}

  ${
    cnnvg.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The vector addition (group) operation of the normed complex vector space
       of complex numbers.  (Contributed by NM, 12-Jan-2008.)
       (New usage is discouraged.) $)
    cnnvg $p |- + = ( +v ` U ) $=
      ( cpv cfv c1st caddc cmul cop eqid vafval cabs fveq2i opex cc cr cvv wcel
      wf absf op1st cnex fex mp2an eqtri addex mulex 3eqtrri ) ACDZAEDZEDFGHZED
      FAUHUHIJUIUJEUIUJKHZEDUJAUKEBLUJKFGMNOKRNPQKPQSUANOPKUBUCTUDLFGUEUFTUG $.
  $}

  ${
    cnnvba.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The base set of the normed complex vector space of complex numbers.
       (Contributed by NM, 7-Nov-2007.)  (New usage is discouraged.) $)
    cnnvba $p |- CC = ( BaseSet ` U ) $=
      ( caddc crn cpv cfv cc cnnvg rneqi cablo wcel cnaddabloOLD ablogrpo ax-mp
      cba cgr cxp ax-addf fdmi eqid grporn bafval 3eqtr4i ) CDAEFZDGAOFZCUDABHI
      CGCJKCPKLCMNGGQGCRSUAAUDUEUETUDTUBUC $.
  $}

  ${
    cnnvs.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The scalar product operation of the normed complex vector space of
       complex numbers.  (Contributed by NM, 12-Jan-2008.)
       (New usage is discouraged.) $)
    cnnvs $p |- x. = ( .sOLD ` U ) $=
      ( cns cfv c1st c2nd caddc cmul cop eqid smfval cabs fveq2i opex cc cr cvv
      wf wcel absf cnex fex mp2an op1st eqtri addex mulex op2nd 3eqtrri ) ACDZA
      EDZFDGHIZFDHUJAUJJKUKULFUKULLIZEDULAUMEBMULLGHNOPLROQSLQSTUAOPQLUBUCUDUEM
      GHUFUGUHUI $.
  $}

  ${
    cnnvnm.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The norm operation of the normed complex vector space of complex
       numbers.  (Contributed by NM, 12-Jan-2008.)
       (New usage is discouraged.) $)
    cnnvnm $p |- abs = ( normCV ` U ) $=
      ( cnmcv cfv c2nd caddc cmul cop cabs eqid nmcvfval fveq2i opex cc cr wcel
      wf cvv absf cnex fex mp2an op2nd 3eqtrri ) ACDZAEDFGHZIHZEDIAUEUEJKAUGEBL
      UFIFGMNOIQNRPIRPSTNORIUAUBUCUD $.
  $}

  ${
    $d x y U $.
    cnnvm.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The vector subtraction operation of the normed complex vector space of
       complex numbers.  (Contributed by NM, 12-Jan-2008.)  (Revised by Mario
       Carneiro, 23-Dec-2013.)  (New usage is discouraged.) $)
    cnnvm $p |- - = ( -v ` U ) $=
      ( vx vy cc cv cmin co cmpo c1 cneg cmul caddc cnsb cfv wcel wa wceq mulm1
      ax-mp adantl oveq2d negsub eqtr2d mpoeq3ia cxp wfn subf ffn fnov mpbi cnv
      wf cnnv cnnvba cnnvg cnnvs eqid nvmfval 3eqtr4i ) CDEECFZDFZGHZIZCDEEVAJK
      VBLHZMHZIZGANOZCDEEVCVFVAEPZVBEPZQZVFVAVBKZMHVCVKVEVLVAMVJVEVLRVIVBSUAUBV
      AVBUCUDUEGEEUFZUGZGVDRVMEGUMVNUHVMEGUITCDEEGUJUKAULPVHVGRABUNCDLAMVHEABUO
      ABUPABUQVHURUSTUT $.
  $}

  ${
    elimnv.1 $e |- X = ( BaseSet ` U ) $.
    elimnv.5 $e |- Z = ( 0vec ` U ) $.
    elimnv.9 $e |- U e. NrmCVec $.
    $( Hypothesis elimination lemma for normed complex vector spaces to assist
       weak deduction theorem.  (Contributed by NM, 16-May-2007.)
       (New usage is discouraged.) $)
    elimnv $p |- if ( A e. X , A , Z ) e. X $=
      ( cnv wcel nvzcl ax-mp elimel ) ADCBHIDCIGBCDEFJKL $.
  $}

  $( Hypothesis elimination lemma for normed complex vector spaces to assist
     weak deduction theorem.  (Contributed by NM, 16-May-2007.)
     (New usage is discouraged.) $)
  elimnvu $p |- if ( U e. NrmCVec , U , <. <. + , x. >. , abs >. )
                 e. NrmCVec $=
    ( caddc cmul cop cabs cnv eqid cnnv elimel ) ABCDEDZFJJGHI $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Induced metric of a normed complex vector space
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d u U $.
    imsval.3 $e |- M = ( -v ` U ) $.
    imsval.6 $e |- N = ( normCV ` U ) $.
    imsval.8 $e |- D = ( IndMet ` U ) $.
    $( Value of the induced metric of a normed complex vector space.
       (Contributed by NM, 11-Sep-2007.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    imsval $p |- ( U e. NrmCVec -> D = ( N o. M ) ) $=
      ( vu cnv wcel cims cfv cnmcv cnsb ccom cv wceq fveq2 coeq12d fvex coeq12i
      df-ims coex fvmpt 3eqtr4g ) BIJBKLBMLZBNLZOZADCOHBHPZMLZUINLZOUHIKUIBQUJU
      FUKUGUIBMRUIBNRSHUBUFUGBMTBNTUCUDGDUFCUGFEUAUE $.
  $}

  ${
    imsdval.1 $e |- X = ( BaseSet ` U ) $.
    imsdval.3 $e |- M = ( -v ` U ) $.
    imsdval.6 $e |- N = ( normCV ` U ) $.
    imsdval.8 $e |- D = ( IndMet ` U ) $.
    $( Value of the induced metric (distance function) of a normed complex
       vector space.  Equation 1 of [Kreyszig] p. 59.  (Contributed by NM,
       11-Sep-2007.)  (Revised by Mario Carneiro, 27-Dec-2014.)
       (New usage is discouraged.) $)
    imsdval $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                  ( A D B ) = ( N ` ( A M B ) ) ) $=
      ( cnv wcel w3a cop cfv co ccom wceq df-ov imsval 3ad2ant1 fveq1d cxp nvmf
      wf wa opelxpi fvco3 syl2an 3impb eqtrd fveq2i 3eqtr4g ) DLMZAGMZBGMZNZABO
      ZCPZUSEPZFPZABCQABEQZFPURUTUSFERZPZVBURUSCVDUOUPCVDSUQCDEFIJKUAUBUCUOUPUQ
      VEVBSZUOGGUDZGEUFUSVGMVFUPUQUGDEGHIUEABGGUHVGGUSFEUIUJUKULABCTVCVAFABETUM
      UN $.
  $}

  ${
    imsdval2.1 $e |- X = ( BaseSet ` U ) $.
    imsdval2.2 $e |- G = ( +v ` U ) $.
    imsdval2.4 $e |- S = ( .sOLD ` U ) $.
    imsdval2.6 $e |- N = ( normCV ` U ) $.
    imsdval2.8 $e |- D = ( IndMet ` U ) $.
    $( TODO $)
    $( Value of the distance function of the induced metric of a normed complex
       vector space.  Equation 1 of [Kreyszig] p. 59.  (Contributed by NM,
       28-Nov-2006.)  (New usage is discouraged.) $)
    imsdval2 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                  ( A D B ) = ( N ` ( A G ( -u 1 S B ) ) ) ) $=
      ( cnv wcel w3a co cnsb cfv c1 cneg eqid imsdval nvmval fveq2d eqtrd ) ENO
      AHOBHOPZABCQABERSZQZGSATUABDQFQZGSABCEUHGHIUHUBZLMUCUGUIUJGABDEFUHHIJKUKU
      DUEUF $.
  $}

  ${
    nvnd.1 $e |- X = ( BaseSet ` U ) $.
    nvnd.5 $e |- Z = ( 0vec ` U ) $.
    nvnd.6 $e |- N = ( normCV ` U ) $.
    nvnd.8 $e |- D = ( IndMet ` U ) $.
    $( The norm of a normed complex vector space expressed in terms of the
       distance function of its induced metric.  Problem 1 of [Kreyszig] p. 63.
       (Contributed by NM, 4-Dec-2006.)  (New usage is discouraged.) $)
    nvnd $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( N ` A ) = ( A D Z ) ) $=
      ( cnv wcel wa co cnsb cfv wceq adantr eqid mpd3an3 nvzcl imsdval cneg cns
      c1 cpv nvmval cc neg1cn nvsz mpan2 oveq2d nv0rid 3eqtrd fveq2d eqtr2d ) C
      KLZAELZMZAFBNZAFCOPZNZDPZADPUQURFELZUTVCQUQVDURCEFGHUARZAFBCVADEGVASZIJUB
      TUSVBADUSVBAUEUCZFCUDPZNZCUFPZNZAFVJNZAUQURVDVBVKQVEAFVHCVJVAEGVJSZVHSZVF
      UGTUQVKVLQURUQVIFAVJUQVGUHLVIFQUIVGVHCFVNHUJUKULRACVJEFGVMHUMUNUOUP $.
  $}

  ${
    imsdfn.1 $e |- X = ( BaseSet ` U ) $.
    imsdfn.8 $e |- D = ( IndMet ` U ) $.
    $( Mapping for the induced metric distance function of a normed complex
       vector space.  (Contributed by NM, 29-Nov-2006.)
       (New usage is discouraged.) $)
    imsdf $p |- ( U e. NrmCVec -> D : ( X X. X ) --> RR ) $=
      ( cnv wcel cxp cr wf cnmcv cfv cnsb ccom eqid nvf nvmf fco syl2anc imsval
      feq1d mpbird ) BFGZCCHZIAJUDIBKLZBMLZNZJZUCCIUEJUDCUFJUHBUECDUEOZPBUFCDUF
      OZQUDCIUEUFRSUCUDIAUGABUFUEUJUIETUAUB $.
  $}

  ${
    $d x y z D $.  $d x y z X $.
    imsmetlem.1 $e |- X = ( BaseSet ` U ) $.
    imsmetlem.2 $e |- G = ( +v ` U ) $.
    imsmetlem.7 $e |- M = ( inv ` G ) $.
    imsmetlem.4 $e |- S = ( .sOLD ` U ) $.
    imsmetlem.5 $e |- Z = ( 0vec ` U ) $.
    imsmetlem.6 $e |- N = ( normCV ` U ) $.
    imsmetlem.8 $e |- D = ( IndMet ` U ) $.
    imsmetlem.9 $e |- U e. NrmCVec $.
    $( Lemma for ~ imsmet .  (Contributed by NM, 29-Nov-2006.)
       (New usage is discouraged.) $)
    imsmetlem $p |- D e. ( Met ` X ) $=
      ( wcel co wceq mp3an1 vx vy vz cba fvexi cnv cxp cr wf imsdf ax-mp cv cc0
      wa c1 cfv imsdval2 eqeq1d wb cc neg1cn nvscl mp3an12 nvgcl sylan2 sylancr
      cneg nvz nvzcl w3a nvrcan mpan mp3an2 sylancom simpl adantl simpr syl3anc
      nvass nvlinv oveq2d nv0rid adantr 3eqtrd nv0lid eqeq12d bitr3d 3bitrd cle
      caddc syl2anc 3adant3 3adant2 nvtri 3adant1 3ad2ant3 oveq1d eqtr3d fveq2d
      wbr simp1 eqtr4d nvdif eqtrd oveq12d 3brtr4d 3coml ismeti ) UAUBUCAGGCUDI
      UECUFQZGGUGUHAUIPACGIOUJUKUAULZGQZUBULZGQZUNZXJXLARZUMSXJUOVGZXLBRZDRZFUP
      ZUMSZXRHSZXJXLSZXNXOXSUMXIXKXMXOXSSZPXJXLABCDFGIJLNOUQTZURXNXIXRGQZXTYAUS
      PXMXKXQGQZYEXIXPUTQZXMYFPVAXPXLBCGILVBVCZXIXKYFYEPXJXQCDGIJVDTVEZXRCFGHIM
      NVHVFXNXRXLDRZHXLDRZSZYAYBXKXMYEYLYAUSZYIYEHGQZXMYMXIYNPCGHIMVIUKXIYEYNXM
      VJYMPXRHXLCDGIJVKVLVMVNXNYJXJYKXLXNYJXJXQXLDRZDRZXJHDRZXJXNXKYFXMYJYPSZXK
      XMVOXMYFXKYHVPXKXMVQXIXKYFXMVJYRPXJXQXLCDGIJVSVLVRXNYOHXJDXMYOHSZXKXIXMYS
      PXLBCDGHIJLMVTVLVPWAXKYQXJSZXMXIXKYTPXJCDGHIJMWBVLZWCWDXMYKXLSZXKXIXMUUBP
      XLCDGHIJMWEVLVPWFWGWHUCULZGQZXKXMXOUUCXJARZUUCXLARZWJRZWIWTUUDXKXMVJZXJXP
      UUCBRZDRZUUCXQDRZDRZFUPZUUJFUPZUUKFUPZWJRZXOUUGWIUUHUUJGQZUUKGQZUUMUUPWIW
      TZUUDXKUUQXMUUDXKUNZXKUUIGQZUUQUUDXKVQZUUDUVAXKXIYGUUDUVAPVAXPUUCBCGILVBV
      CWCZXIXKUVAUUQPXJUUICDGIJVDTWKWLZUUDXMUURXKXMUUDYFUURYHXIUUDYFUURPUUCXQCD
      GIJVDTVEWMXIUUQUURUUSPUUJUUKCDFGIJNWNTWKUUHXOXSUUMXKXMYCUUDYDWOUUHUULXRFU
      UHUUJUUCDRZXQDRZUULXRUUHUUQUUDYFUVFUULSZUVDUUDXKXMXAXMUUDYFXKYHWPXIUUQUUD
      YFVJUVGPUUJUUCXQCDGIJVSVLVRUUHUVEXJXQDUUDXKUVEXJSXMUUTUVEXJUUIUUCDRZDRZYQ
      XJUUTXKUVAUUDUVEUVISZUVBUVCUUDXKVOXIXKUVAUUDVJUVJPXJUUIUUCCDGIJVSVLVRUUTU
      VHHXJDUUDUVHHSZXKXIUUDUVKPUUCBCDGHIJLMVTVLWCWAXKYTUUDUUAVPWDWLWQWRWSXBUUH
      UUEUUNUUFUUOWJUUDXKUUEUUNSXMUUTUUEUUCXPXJBRDRFUPZUUNXIUUDXKUUEUVLSPUUCXJA
      BCDFGIJLNOUQTXIUUDXKUVLUUNSPUUCXJBCDFGIJLNXCTXDWLUUDXMUUFUUOSZXKXIUUDXMUV
      MPUUCXLABCDFGIJLNOUQTWMXEXFXGXH $.
  $}

  ${
    imsmet.1 $e |- X = ( BaseSet ` U ) $.
    imsmet.8 $e |- D = ( IndMet ` U ) $.
    $( The induced metric of a normed complex vector space is a metric space.
       Part of Definition 2.2-1 of [Kreyszig] p. 58.  (Contributed by NM,
       4-Dec-2006.)  (Revised by Mario Carneiro, 10-Sep-2015.)
       (New usage is discouraged.) $)
    imsmet $p |- ( U e. NrmCVec -> D e. ( Met ` X ) ) $=
      ( cnv wcel cims cfv cmet caddc cmul cop cabs cif wceq fveq2 eqtrid eqid
      cba fveq2d eleq12d cns cpv cnmcv cn0v elimnvu imsmetlem dedth eqeltrid
      cgn ) BFGZABHIZCJIZEULUMUNGULBKLMNMZOZHIZUPTIZJIZGBUOBUPPZUMUQUNUSBUPHQUT
      CURJUTCBTIURDBUPTQRUAUBUQUPUCIZUPUPUDIZVBUKIZUPUEIZURUPUFIZURSVBSVCSVASVE
      SVDSUQSBUGUHUIUJ $.

    $( The induced metric of a normed complex vector space is an extended
       metric space.  (Contributed by Mario Carneiro, 10-Sep-2015.)
       (New usage is discouraged.) $)
    imsxmet $p |- ( U e. NrmCVec -> D e. ( *Met ` X ) ) $=
      ( cnv wcel cmet cfv cxmet imsmet metxmet syl ) BFGACHIGACJIGABCDEKACLM $.
  $}

  ${
    cnims.6 $e |- U = <. <. + , x. >. , abs >. $.
    cnims.7 $e |- D = ( abs o. - ) $.
    $( The metric induced on the complex numbers. ~ cnmet proves that it is a
       metric.  (Contributed by Steve Rodriguez, 5-Dec-2006.)  (Revised by NM,
       15-Jan-2008.)  (New usage is discouraged.) $)
    cnims $p |- D = ( IndMet ` U ) $=
      ( cabs cmin ccom cims cfv wcel wceq cnnv cnnvm cnnvnm imsval ax-mp eqtr4i
      cnv eqid ) AEFGZBHIZDBRJUATKBCLUABFEBCMBCNUASOPQ $.
  $}

  ${
    $d r s w x y z C $.  $d r s w x y z G $.  $d r s w x y z J $.
    $d r s w x y z U $.
    vacn.c $e |- C = ( IndMet ` U ) $.
    vacn.j $e |- J = ( MetOpen ` C ) $.
    vacn.g $e |- G = ( +v ` U ) $.
    $( Vector addition is jointly continuous in both arguments.  (Contributed
       by Jeff Hankins, 16-Jun-2009.)  (Revised by Mario Carneiro,
       10-Sep-2015.)  (New usage is discouraged.) $)
    vacn $p |- ( U e. NrmCVec -> G e. ( ( J tX J ) Cn J ) ) $=
      ( vz vw wcel co cfv cv clt wbr wa wral crp cr syl3anc vx vs vy vr cnv ctx
      ccn cba wf wi wrex eqid nvgf c2 cdiv rphalfcl adantl caddc simplll imsmet
      cxp cmet syl simplrl adantr simprl simplrr simprr rpre ad2antlr lt2halves
      metcl cle cnsb cnmcv nvmcl nvtri nvgcl imsdval nvaddsub4 syl122anc fveq2d
      wceq eqtrd oveq12d 3brtr4d readdcld lelttr mpand ralrimivva breq2 anbi12d
      syld imbi1d 2ralbidv syl2anc ralrimiva cxmet wb imsxmet txmetcn mpbir2and
      rspcev ) BUEJZCDDUFKDUGKJZBUHLZXFVAXFCUIZUAMZHMZAKZUBMZNOZUCMZIMZAKZXKNOZ
      PZXHXMCKZXIXNCKZAKZUDMZNOZUJZIXFQHXFQZUBRUKZUDRQZUCXFQUAXFQZBCXFXFULZGUMX
      DYFUAUCXFXFXDXHXFJZXMXFJZPZPZYEUDRYLYARJZPZYAUNUOKZRJZXJYONOZXOYONOZPZYBU
      JZIXFQHXFQZYEYMYPYLYAUPUQYNYTHIXFXFYNXIXFJZXNXFJZPZPZYSXJXOURKZYANOZYBUUE
      XJSJZXOSJZYASJZYSUUGUJUUEAXFVBLJZYIUUBUUHUUEXDUUKXDYKYMUUDUSZABXFYHEUTVCZ
      YNYIUUDXDYIYJYMVDVEZYNUUBUUCVFZXHXIAXFVLTZUUEUUKYJUUCUUIUUMYNYJUUDXDYIYJY
      MVGVEZYNUUBUUCVHZXMXNAXFVLTZYMUUJYLUUDYAVIVJZXJXOYAVKTUUEXTUUFVMOZUUGYBUU
      EXHXIBVNLZKZXMXNUVBKZCKZBVOLZLZUVCUVFLZUVDUVFLZURKZXTUUFVMUUEXDUVCXFJZUVD
      XFJZUVGUVJVMOUULUUEXDYIUUBUVKUULUUNUUOXHXIBUVBXFYHUVBULZVPTUUEXDYJUUCUVLU
      ULUUQUURXMXNBUVBXFYHUVMVPTUVCUVDBCUVFXFYHGUVFULZVQTUUEXTXRXSUVBKZUVFLZUVG
      UUEXDXRXFJZXSXFJZXTUVPWCUULUUEXDYIYJUVQUULUUNUUQXHXMBCXFYHGVRTZUUEXDUUBUU
      CUVRUULUUOUURXIXNBCXFYHGVRTZXRXSABUVBUVFXFYHUVMUVNEVSTUUEUVOUVEUVFUUEXDYI
      YJUUBUUCUVOUVEWCUULUUNUUQUUOUURXHXMXIXNBCUVBXFYHGUVMVTWAWBWDUUEXJUVHXOUVI
      URUUEXDYIUUBXJUVHWCUULUUNUUOXHXIABUVBUVFXFYHUVMUVNEVSTUUEXDYJUUCXOUVIWCUU
      LUUQUURXMXNABUVBUVFXFYHUVMUVNEVSTWEWFUUEXTSJZUUFSJUUJUVAUUGPYBUJUUEUUKUVQ
      UVRUWAUUMUVSUVTXRXSAXFVLTUUEXJXOUUPUUSWGUUTXTUUFYAWHTWIWMWJYDUUAUBYORXKYO
      WCZYCYTHIXFXFUWBXQYSYBUWBXLYQXPYRXKYOXJNWKXKYOXONWKWLWNWOXCWPWQWJXDAXFWRL
      JZUWCUWCXEXGYGPWSABXFYHEWTZUWDUWDUAUCUDUBIHAAACDDDXFXFXFFFFXATXB $.
  $}

  ${
    $d d e x y C $.  $d d e x y J $.  $d d e x y K $.  $d d e x y N $.
    $d d e x y U $.
    nmcvcn.1 $e |- N = ( normCV ` U ) $.
    nmcvcn.2 $e |- C = ( IndMet ` U ) $.
    nmcvcn.j $e |- J = ( MetOpen ` C ) $.
    nmcvcn.k $e |- K = ( topGen ` ran (,) ) $.
    $( The norm of a normed complex vector space is a continuous function.
       (Contributed by NM, 16-May-2007.)  (Proof shortened by Mario Carneiro,
       10-Jan-2014.)  (New usage is discouraged.) $)
    nmcvcn $p |- ( U e. NrmCVec -> N e. ( J Cn K ) ) $=
      ( vx vy vd ve wcel co cfv cr crp eqid wa cnv ccn cba wf clt wbr cabs cmin
      cv ccom cxp cres wi wral wrex nvf simprr cle w3a nvcl anim12d remet metcl
      ex cmet mp3an1 syl6 3impib imsmet syl3an1 c1 cneg cns cpv nvabs remetdval
      wceq syl imsdval2 3brtr4d jca31 3expa rpre lelttr expdimp an32s ralrimdva
      syl2an impr breq2 rspceaimv syl2anc ralrimivva wb imsxmet rexmet cioo crn
      cxmet ctg cmopn tgioo eqtri metcn sylancl mpbir2and ) BUANZECDUBONZBUCPZQ
      EUDZJUIZKUIZAOZLUIZUEUFZXKEPZXLEPZUGUHUJQQUKULZOZMUIZUEUFZUMKXIUNLRUOZMRU
      NJXIUNZBEXIXISZFUPXGYBJMXIRXGXKXINZXTRNZTTYFXMXTUEUFZYAUMZKXIUNZYBXGYEYFU
      QXGYEYFYIXGYETZYFYHKXIYJXLXINZTZYFYHYLXSQNZXMQNZTZXSXMURUFZTZXTQNZYHYFXGY
      EYKYQXGYEYKUSZYMYNYPXGYEYKYMXGYEYKTXPQNZXQQNZTZYMXGYEYTYKUUAXGYEYTXKBEXIY
      DFUTVDXGYKUUAXLBEXIYDFUTVDVAZXRQVEPNYTUUAYMXRXRSZVBXPXQXRQVCVFVGVHXGAXIVE
      PNYEYKYNABXIYDGVIXKXLAXIVCVJYSXPXQUHOUGPZXKVKVLXLBVMPZOBVNPZOEPXSXMURXKXL
      UUFBUUGEXIYDUUGSZUUFSZFVOYSUUBXSUUEVQXGYEYKUUBUUCVHXPXQXRUUDVPVRXKXLAUUFB
      UUGEXIYDUUHUUIFGVSVTWAWBXTWCYOYRYPYHYOYRTYPYGYAYMYNYRYPYGTYAUMXSXMXTWDWBW
      EWFWHVDWGWIXOYGYALKXTRXIXNXTXMUEWJWKWLWMXGAXIWSPNXRQWSPNXHXJYCTWNABXIYDGW
      OXRUUDWPJMLKAXRECDXIQHDWQWRWTPXRXAPZIXRUUJUUDUUJSXBXCXDXEXF $.
  $}

  ${
    nmcnc.1 $e |- N = ( normCV ` U ) $.
    nmcnc.2 $e |- C = ( IndMet ` U ) $.
    nmcnc.j $e |- J = ( MetOpen ` C ) $.
    nmcnc.k $e |- K = ( TopOpen ` CCfld ) $.
    $( The norm of a normed complex vector space is a continuous function to
       ` CC ` .  (For ` RR ` , see ~ nmcvcn .)  (Contributed by NM,
       12-Aug-2007.)  (New usage is discouraged.) $)
    nmcnc $p |- ( U e. NrmCVec -> N e. ( J Cn K ) ) $=
      ( cnv wcel cr crest co ccn ctop wss cnfldtop cnrest2r ax-mp tgioo2 eqcomi
      cioo crn ctg cfv nmcvcn sselid ) BJKCDLMNZONZCDONZEDPKUJUKQDIRLCDSTABCUIE
      FGHUCUDUEUFUIDIUAUBUGUH $.
  $}

  ${
    $d r s w x y z C $.  $d r s w x y z J $.  $d s w z T $.  $d r x y U $.
    $d r s w x y z K $.  $d r s w x y z S $.  $d r s w x y z X $.
    smcn.c $e |- C = ( IndMet ` U ) $.
    smcn.j $e |- J = ( MetOpen ` C ) $.
    smcn.s $e |- S = ( .sOLD ` U ) $.
    smcn.k $e |- K = ( TopOpen ` CCfld ) $.
    ${
      smcn.x $e |- X = ( BaseSet ` U ) $.
      smcn.n $e |- N = ( normCV ` U ) $.
      smcn.u $e |- U e. NrmCVec $.
      smcn.t $e |- T = ( 1 / ( 1 + ( ( ( ( N ` y ) +
                         ( abs ` x ) ) + 1 ) / r ) ) ) $.
      $( Lemma for ~ smcn .  (Contributed by Mario Carneiro, 5-May-2014.)
         (Revised by Mario Carneiro, 10-Sep-2015.)
         (New usage is discouraged.) $)
      smcnlem $p |- S e. ( ( K tX J ) Cn J ) $=
        ( co vz vs vw ctx ccn wcel cc cxp wf cv cabs cmin ccom clt wbr wral crp
        wa wi wrex cnv nvsf ax-mp c1 cfv caddc cdiv cr simpr nvcl sylancr abscl
        1rp adantr readdcld cc0 cle nvge0 absge0 addge0d ge0p1rpd rpdivcl sylan
        rpaddcl rpreccld eqeltrid cmet imsmet a1i simplll simpllr nvscl syl3anc
        simprll simprlr metcl rpre ad2antlr mettri syl13anc abscld peano2re syl
        cmul rpred remulcld cnsb subcld eqid nvmcl abssubd wceq cnmetdval eqtrd
        syl2anc simprrl eqbrtrrd ltled eqbrtrd lemul1ad mulcomd breqtrd absge0d
        rpcnd recnd pncan3d fveq2d abstrid 1red letrd cneg neg1cn oveq2d oveq1d
        imsdval nvs 3eqtr2d lelttrd breq2 cxmet ltaddrp mpbid eqbrtrid leadd2dd
        1re recgt1d simprrr lemul12ad le2addd cpv imsdval2 mulcl mulm1d negsubd
        nvdir nvsass 3eqtr3d oveq12d 1cnd addassd adddird 3brtr4d oveq2i rpne0d
        nvmdi divrecd eqtr4id simplr ltp1d addcomd ltdiv23d expr anbi12d imbi1d
        ralrimivva 2ralbidv rspcev ralrimiva rgen2 wb imsxmet cnfldtopn txmetcn
        cnxmet mp3an mpbir2an ) DHGUDTGUETUFZUGJUHJDUIZAUJZUAUJZUKULUMZTZUBUJZU
        NUOZBUJZUCUJZCTZUWMUNUOZURZUWIUWODTZUWJUWPDTZCTZKUJZUNUOZUSZUCJUPUAUGUP
        ZUBUQUTZKUQUPZBJUPAUGUPZFVAUFZUWHRDFJPNVBVCUXHABUGJUWIUGUFZUWOJUFZURZUX
        GKUQUXMUXCUQUFZURZEUQUFZUWLEUNUOZUWQEUNUOZURZUXDUSZUCJUPUAUGUPZUXGUXOEV
        DVDUWOIVEZUWIUKVEZVFTZVDVFTZUXCVGTZVFTZVGTZUQSUXOUYGUXOVDUQUFUYFUQUFZUY
        GUQUFZVMUXMUYEUQUFUXNUYIUXMUYDUXMUYBUYCUXMUXJUXLUYBVHUFZRUXKUXLVIZUWOFI
        JPQVJZVKZUXKUYCVHUFZUXLUWIVLVNZVOUXMUYBUYCUYNUYPUXMUXJUXLVPUYBVQUOZRUYL
        UWOFIJPQVRZVKUXKVPUYCVQUOUXLUWIVSVNVTWAUYEUXCWBWCZVDUYFWDVKZWEWFZUXOUXT
        UAUCUGJUXOUWJUGUFZUWPJUFZURZUXSUXDUXOVUDUXSURZURZUXBUWTUWJUWODTZCTZVUGU
        XACTZVFTZUXCVUFCJWGVEUFZUWTJUFZUXAJUFZUXBVHUFVUKVUFUXJVUKRCFJPLWHVCWIZV
        UFUXJUXKUXLVULUXJVUFRWIZUXKUXLUXNVUEWJZUXKUXLUXNVUEWKZUWIUWODFJPNWLWMZV
        UFUXJVUBVUCVUMVUOUXOVUBVUCUXSWNZUXOVUBVUCUXSWOZUWJUWPDFJPNWLWMZUWTUXACJ
        WPWMVUFVUHVUIVUFVUKVULVUGJUFZVUHVHUFVUNVURVUFUXJVUBUXLVVBVUOVUSVUQUWJUW
        ODFJPNWLWMZUWTVUGCJWPWMVUFVUKVVBVUMVUIVHUFVUNVVCVVAVUGUXACJWPWMVOZUXNUX
        CVHUFUXMVUEUXCWQWRZVUFVUKVULVUMVVBUXBVUJVQUOVUNVURVVAVVCUWTUXAVUGCJWSWT
        VUFVUJUYEEXDTZUXCVVDVUFUYEEVUFUYDVHUFUYEVHUFVUFUYBUYCVUFUXJUXLUYKRVUQUY
        MVKZVUFUWIVUPXAZVOUYDXBXCZVUFEUXOUXPVUEVUAVNZXEZXFVVEVUFUWIUWJULTZUKVEZ
        UYBXDTZUWJUKVEZUWOUWPFXGVEZTZIVEZXDTZVFTUYBEXDTZUYCVDVFTZEXDTZVFTZVUJVV
        FVQVUFVVNVVSVVTVWBVUFVVMUYBVUFVVLVUFUWIUWJVUPVUSXHZXAZVVGXFVUFVVOVVRVUF
        UWJVUSXAZVUFUXJVVQJUFZVVRVHUFRVUFUXJUXLVUCVWGVUOVUQVUTUWOUWPFVVPJPVVPXI
        ZXJWMZVVQFIJPQVJVKZXFVUFUYBEVVGVVKXFVUFVWAEVUFUYOVWAVHUFVVHUYCXBXCZVVKX
        FVUFVVNEUYBXDTVVTVQVUFVVMEUYBVWEVVKVVGVUFUXJUXLUYQRVUQUYRVKVUFVVMUWJUWI
        ULTZUKVEZEVQVUFUWIUWJVUPVUSXKZVUFVWMEVUFVWLVUFUWJUWIVUSVUPXHZXAZVVKVUFU
        WLVWMEUNVUFUWLVVMVWMVUFUXKVUBUWLVVMXLVUPVUSUWIUWJUWKUWKXIXMXOVWNXNUXOVU
        DUXQUXRXPXQXRZXSXTVUFEUYBVUFEVVJYDZVUFUYBVVGYEZYAYBVUFVVOVWAVVREVWFVWKV
        WJVVKVUFUWJVUSYCVUFUXJVWGVPVVRVQUORVWIVVQFIJPQVRVKVUFVVOUYCVWMVFTZVWAVW
        FVUFUYCVWMVVHVWPVOVWKVUFUWIVWLVFTZUKVEVVOVWTVQVUFVXAUWJUKVUFUWIUWJVUPVU
        SYFYGVUFUWIVWLVUPVWOYHXQVUFVWMVDUYCVWPVUFYIZVVHVUFVWMEVDVWPVVKVXBVWQVUF
        EVDVVKVXBVUFEUYHVDUNSVUFVDUYGUNUOZUYHVDUNUOVUFVDVHUFUYIVXCUUEUXOUYIVUEU
        YSVNZVDUYFUUAVKVUFUYGUXOUYJVUEUYTVNZUUFUUBUUCXRYJUUDYJVUFVVREVWJVVKVUFU
        WQVVREUNVUFUXJUXLVUCUWQVVRXLVUOVUQVUTUWOUWPCFVVPIJPVWHQLYOWMUXOVUDUXQUX
        RUUGXQXRUUHUUIVUFVUHVVNVUIVVSVFVUFVUHUWTVDYKZVUGDTZFUUJVEZTZIVEZVVLUWOD
        TZIVEZVVNVUFUXJVULVVBVUHVXJXLVUOVURVVCUWTVUGCDFVXHIJPVXHXIZNQLUUKWMVUFV
        XKVXIIVUFUWIVXFUWJXDTZVFTZUWODTZUWTVXNUWODTZVXHTZVXKVXIVUFUXJUXKVXNUGUF
        ZUXLVXPVXRXLVUOVUPVUFVXFUGUFZVUBVXSYLVUSVXFUWJUULVKVUQUWIVXNUWODFVXHJPV
        XMNUUOWTVUFVXOVVLUWODVUFVXOUWIUWJYKZVFTVVLVUFVXNVYAUWIVFVUFUWJVUSUUMYMV
        UFUWIUWJVUPVUSUUNXNYNVUFVXQVXGUWTVXHVUFUXJVXTVUBUXLVXQVXGXLVUOVXTVUFYLW
        IVUSVUQVXFUWJUWODFJPNUUPWTYMUUQYGVUFUXJVVLUGUFUXLVXLVVNXLVUOVWDVUQVVLUW
        ODFIJPNQYPWMYQVUFVUIVUGUXAVVPTZIVEZUWJVVQDTZIVEZVVSVUFUXJVVBVUMVUIVYCXL
        VUOVVCVVAVUGUXACFVVPIJPVWHQLYOWMVUFVYDVYBIVUFUXJVUBUXLVUCVYDVYBXLVUOVUS
        VUQVUTUWJUWOUWPDFVVPJPVWHNUVEWTYGVUFUXJVUBVWGVYEVVSXLVUOVUSVWIUWJVVQDFI
        JPNQYPWMYQUURVUFVVFUYBVWAVFTZEXDTVWCVUFUYEVYFEXDVUFUYBUYCVDVWSVUFUYCVVH
        YEVUFUUSZUUTYNVUFUYBVWAEVWSVUFVWAVWKYEVWRUVAXNUVBVUFVVFUYEUYGVGTZUXCUNV
        UFVVFUYEUYHXDTVYHEUYHUYEXDSUVCVUFUYEUYGVUFUYEVVIYEVUFUYGVXEYDVUFUYGVXEU
        VDUVFUVGVUFUYEUXCUYGVVIUXMUXNVUEUVHVXEVUFUYFUYFVDVFTUYGUNVUFUYFVUFUYFVX
        DXEUVIVUFUYFVDVUFUYFVXDYDVYGUVJYBUVKXSYRYRUVLUVOUXFUYAUBEUQUWMEXLZUXEUX
        TUAUCUGJVYIUWSUXSUXDVYIUWNUXQUWRUXRUWMEUWLUNYSUWMEUWQUNYSUVMUVNUVPUVQXO
        UVRUVSUWKUGYTVEUFCJYTVEUFZVYJUWGUWHUXIURUVTUWDUXJVYJRCFJPLUWAVCZVYKABKU
        BUCUAUWKCCDHGGUGJJHOUWBMMUWCUWEUWF $.
    $}

    $( Scalar multiplication is jointly continuous in both arguments.
       (Contributed by NM, 16-Jun-2009.)  (Revised by Mario Carneiro,
       5-May-2014.)  (New usage is discouraged.) $)
    smcn $p |- ( U e. NrmCVec -> S e. ( ( K tX J ) Cn J ) ) $=
      ( wcel ctx co ccn caddc cns cfv cims cmopn eqtrid eqid vx vy cnv cmul cop
      vr cabs cif wceq fveq2 fveq2d oveq2d oveq12d eleq12d c1 cv cnmcv cdiv cba
      elimnvu smcnlem dedth ) CUCJZBEDKLZDMLZJVCCNUDUEUGUEZUHZOPZEVGQPZRPZKLZVJ
      MLZJCVFCVGUIZBVHVEVLVMBCOPVHHCVGOUJSVMVDVKDVJMVMDVJEKVMDARPVJGVMAVIRVMACQ
      PVIFCVGQUJSUKSZULVNUMUNUAUBVIVHUOUOUBUPVGUQPZPUAUPUGPNLUONLUFUPURLNLURLZV
      GVJEVOVGUSPZUFVITVJTVHTIVQTVOTCUTVPTVAVB $.
  $}

  ${
    $d x y J $.  $d x y M $.  $d x y U $.
    vmcn.c $e |- C = ( IndMet ` U ) $.
    vmcn.j $e |- J = ( MetOpen ` C ) $.
    vmcn.m $e |- M = ( -v ` U ) $.
    $( Vector subtraction is jointly continuous in both arguments.
       (Contributed by Mario Carneiro, 6-May-2014.)
       (New usage is discouraged.) $)
    vmcn $p |- ( U e. NrmCVec -> M e. ( ( J tX J ) Cn J ) ) $=
      ( vx vy cnv wcel cba cfv cv co eqid ctopon cc a1i cnmpt22f c1 cns cpv ctx
      cneg cmpo ccn nvmfval cxmet imsxmet mopntopon syl ccnfld ctopn cnfldtopon
      cnmpt1st neg1cn cnmpt2c cnmpt2nd smcn vacn eqeltrd ) BJKZDHIBLMZVDHNZUAUE
      ZINZBUBMZOZBUCMZOUFCCUDOCUGOHIVHBVJDVDVDPZVJPZVHPZGUHVCHIVEVIVJCCCCCVDVDV
      CAVDUIMKCVDQMKABVDVKEUJACVDFUKULZVNVCHICCVDVDVNVNUPVCHIVFVGVHCCUMUNMZCCVD
      VDVNVNVCHIVFCCVOVDVDRVNVNVORQMKVCVOVOPZUOSVFRKVCUQSURVCHICCVDVDVNVNUSAVHB
      CVOEFVMVPUTTABVJCEFVLVATVB $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Inner product
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c .iOLD $.

  $( Extend class notation with the class inner product functions. $)
  cdip $a class .iOLD $.

  ${
    $d k u x y $.
    $( Define a function that maps a normed complex vector space to its inner
       product operation in case its norm satisfies the parallelogram identity
       (otherwise the operation is still defined, but not meaningful).  Based
       on Exercise 4(a) of [ReedSimon] p. 63 and Theorem 6.44 of [Ponnusamy]
       p. 361.  Vector addition is ` ( 1st `` w ) ` , the scalar product is
       ` ( 2nd `` w ) ` , and the norm is ` n ` .  (Contributed by NM,
       10-Apr-2007.)  (New usage is discouraged.) $)
    df-dip $a |- .iOLD = ( u e. NrmCVec |->
      ( x e. ( BaseSet ` u ) , y e. ( BaseSet ` u ) |->
    ( sum_ k e. ( 1 ... 4 ) ( ( _i ^ k ) x. ( ( ( normCV ` u ) ` ( x ( +v ` u )
        ( ( _i ^ k ) ( .sOLD ` u ) y ) ) ) ^ 2 ) ) / 4 ) ) ) $.

$(
    df-dip $a |- .iOLD = { <. x , y >. | ( x e. NrmCVec /\ E. g E. s E. n
            ( x = <. <. g , s >. , n >. /\ y = { <. <. a , b >. , c >. |
            ( ( a e. dom n /\ b e. dom n ) /\ c = ( sum_ k e. ( 1 ... 4 )
             ( ( _i ^ k ) x. ( ( n ` ( a g ( ( _i ^ k ) s b ) ) ) ^ 2 ) )
              / 4 ) ) } ) ) } $.

    df-dip $a |- .iOLD = { <. x , y >. | ( x e. NrmCVec /\ E. g E. s E. n
            ( x = <. <. g , s >. , n >. /\ y = { <. <. a , b >. , c >. |
            ( ( a e. dom n /\ b e. dom n ) /\ c =
                ( ( ( ( ( n ` ( a g b ) ) ^ 2 ) +
                ( ( n ` ( a g ( -u 1 s b ) ) ) ^ 2 ) ) +
                ( _i x. ( ( ( n ` ( a g ( _i s b ) ) ) ^ 2 ) +
                ( ( n ` ( a g ( -u _i s b ) ) ) ^ 2 ) ) ) ) / 4 ) ) } ) ) } $.
$)
  $}

  ${
    $d k u x y G $.  $d k u x y N $.  $d k u x y S $.  $d k u x y U $.
    $d k x y A $.  $d k x y B $.  $d k u x y X $.
    dipfval.1 $e |- X = ( BaseSet ` U ) $.
    dipfval.2 $e |- G = ( +v ` U ) $.
    dipfval.4 $e |- S = ( .sOLD ` U ) $.
    dipfval.6 $e |- N = ( normCV ` U ) $.
    dipfval.7 $e |- P = ( .iOLD ` U ) $.
    $( The inner product function on a normed complex vector space.  The
       definition is meaningful for vector spaces that are also inner product
       spaces, i.e. satisfy the parallelogram law.  (Contributed by NM,
       10-Apr-2007.)  (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    dipfval $p |- ( U e. NrmCVec -> P = ( x e. X , y e. X |->
      ( sum_ k e. ( 1 ... 4 ) ( ( _i ^ k ) x.
        ( ( N ` ( x G ( ( _i ^ k ) S y ) ) ) ^ 2 ) ) / 4 ) ) ) $=
      ( cfv c4 co cv cexp cba vu cnv wcel cdip c1 cfz ci cmul csu cdiv cmpo cns
      c2 cnmcv wceq fveq2 eqtr4di eqidd oveqd oveq123d fveq12d oveq1d sumeq2sdv
      cpv oveq2d mpoeq123dv df-dip fvexi mpoex fvmpt eqtrid ) EUBUCCEUDOABIIUEP
      UFQZUGFRSQZARZVMBRZDQZGQZHOZUMSQZUHQZFUIZPUJQZUKZNUAEABUARZTOZWEVLVMVNVMV
      OWDULOZQZWDVDOZQZWDUNOZOZUMSQZUHQZFUIZPUJQZUKWCUBUDWDEUOZABWEWEWOIIWBWPWE
      ETOIWDETUPJUQZWQWPWNWAPUJWPVLWMVTFWPWLVSVMUHWPWKVRUMSWPWIVQWJHWPWJEUNOHWD
      EUNUPMUQWPVNVNWGVPWHGWPWHEVDOGWDEVDUPKUQWPVNURWPWFDVMVOWPWFEULODWDEULUPLU
      QUSUTVAVBVEVCVBVFABUAFVGABIIWBIETJVHZWRVIVJVK $.

    $( Value of the inner product.  The definition is meaningful for normed
       complex vector spaces that are also inner product spaces, i.e. satisfy
       the parallelogram law, although for convenience we define it for any
       normed complex vector space.  The vector (group) addition operation is
       ` G ` , the scalar product is ` S ` , the norm is ` N ` , and the set of
       vectors is ` X ` .  Equation 6.45 of [Ponnusamy] p. 361.  (Contributed
       by NM, 31-Jan-2007.)  (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    ipval $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A P B ) =
                ( sum_ k e. ( 1 ... 4 ) ( ( _i ^ k ) x. ( ( N ` ( A G
                    ( ( _i ^ k ) S B ) ) ) ^ 2 ) ) / 4 ) ) $=
      ( co c4 cexp c2 cmul cdiv vx vy cnv wcel c1 cfz ci cv cfv wceq wa dipfval
      csu cmpo oveqd fvoveq1 oveq1d oveq2d sumeq2sdv oveq2 fveq2d eqid sylan9eq
      ovex ovmpo 3impb ) EUCUDZAIUDZBIUDZABCOZUEPUFOZUGFUHQOZAVLBDOZGOZHUIZRQOZ
      SOZFUMZPTOZUJVGVHVIUKVJABUAUBIIVKVLUAUHZVLUBUHZDOZGOHUIZRQOZSOZFUMZPTOZUN
      ZOVSVGCWHABUAUBCDEFGHIJKLMNULUOUAUBABIIWGVSWHVKVLAWBGOZHUIZRQOZSOZFUMZPTO
      VTAUJZWFWMPTWNVKWEWLFWNWDWKVLSWNWCWJRQVTAWBHGUPUQURUSUQWABUJZWMVRPTWOVKWL
      VQFWOWKVPVLSWOWJVORQWOWIVNHWOWBVMAGWABVLDUTURVAUQURUSUQWHVBVRPTVDVEVCVF
      $.

    $( Lemma for ~ ipval3 .  (Contributed by NM, 1-Feb-2007.)
       (New usage is discouraged.) $)
    ipval2lem2 $p |- ( ( ( U e. NrmCVec /\ A e. X /\ B e. X ) /\ C e. CC ) ->
               ( ( N ` ( A G ( C S B ) ) ) ^ 2 ) e. RR ) $=
      ( cnv wcel w3a cc wa co cfv cr simpl1 simpl2 nvscl 3expa 3adantl2 syl3anc
      3com23 nvgcl nvcl syl2anc resqcld ) FOPZAIPZBIPZQCRPZSZACBETZGTZHUAZURUNU
      TIPZVAUBPUNUOUPUQUCZURUNUOUSIPZVBVCUNUOUPUQUDUNUPUQVDUOUNUPUQVDUNUQUPVDCB
      EFIJLUEUIUFUGAUSFGIJKUJUHUTFHIJMUKULUM $.

    $( Lemma for ~ ipval3 .  (Contributed by NM, 1-Feb-2007.)
       (New usage is discouraged.) $)
    ipval2lem3 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
               ( ( N ` ( A G B ) ) ^ 2 ) e. RR ) $=
      ( wcel c1 co cfv c2 cexp cr cnv w3a wa nvsid oveq2d fveq2d oveq1d 3adant2
      wceq cc ax-1cn ipval2lem2 mpan2 eqeltrrd ) EUANZAHNZBHNZUBZAOBDPZFPZGQZRS
      PZABFPZGQZRSPZTUOUQVBVEUIUPUOUQUCZVAVDRSVFUTVCGVFUSBAFBDEHIKUDUEUFUGUHURO
      UJNVBTNUKABOCDEFGHIJKLMULUMUN $.

    $( Lemma for ~ ipval3 .  (Contributed by NM, 1-Feb-2007.)
       (New usage is discouraged.) $)
    ipval2lem4 $p |- ( ( ( U e. NrmCVec /\ A e. X /\ B e. X ) /\ C e. CC ) ->
               ( ( N ` ( A G ( C S B ) ) ) ^ 2 ) e. CC ) $=
      ( cnv wcel w3a cc wa co cfv c2 cexp ipval2lem2 recnd ) FOPAIPBIPQCRPSACBE
      TGTHUAUBUCTABCDEFGHIJKLMNUDUE $.

    $( Expansion of the inner product value ~ ipval .  (Contributed by NM,
       31-Jan-2007.)  (Revised by Mario Carneiro, 5-May-2014.)
       (New usage is discouraged.) $)
    ipval2 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A P B )
               = ( ( ( ( ( N ` ( A G B ) ) ^ 2 ) -
               ( ( N ` ( A G ( -u 1 S B ) ) ) ^ 2 ) ) +
               ( _i x. ( ( ( N ` ( A G ( _i S B ) ) ) ^ 2 ) -
               ( ( N ` ( A G ( -u _i S B ) ) ) ^ 2 ) ) ) ) / 4 ) ) $=
      ( wcel co c1 ci cexp c2 cmul vk cnv w3a c4 cfz cv cfv csu cdiv cneg caddc
      cmin ipval cc ax-icn ipval2lem4 mpan2 mulcl sylancr neg1cn subcld negsubd
      negicn mulm1d oveq2d mulneg1 oveq12d mp3an1 syl2anc oveq1d sub32d 3eqtr4d
      eqtrd wceq subdi wa nvsid fveq2d 3adant2 ipval2lem3 recnd mullidd cn nnuz
      c3 df-4 oveq2 i4 eqtrdi cn0 nnnn0 expcl adantl sylan2 mulcld df-3 i3 df-2
      i2 cz 1z exp1 ax-mp fsum1 1nn jctil eqidd fsump1i simprd subadd23d eqtr4d
      addcomd ) EUBNZAHNZBHNZUCZABCOPUDUEOQUAUFZROZAXRBDOZFOZGUGZSROZTOZUAUHZUD
      UIOABFOZGUGZSROZAPUJZBDOZFOZGUGZSROZULOZQAQBDOZFOZGUGZSROZAQUJZBDOZFOZGUG
      ZSROZULOZTOZUKOZUDUIOABCDEUAFGHIJKLMUMXPYDUUEUDUIXPQYQTOZYHYLTOZUKOZYRUUB
      TOZUKOZPAPBDOZFOZGUGZSROZTOZUKOZUUDYLULOZYGUKOZYDUUEXPUUJUUQUUOYGUKXPUUFY
      LULOZQUUBTOZUJZUKOUUSUUTULOZUUJUUQXPUUSUUTXPUUFYLXPQUNNZYQUNNZUUFUNNZUOXP
      UVCUVDUOABQCDEFGHIJKLMUPUQZQYQURUSZXPYHUNNYLUNNUTABYHCDEFGHIJKLMUPUQZVAXP
      UVCUUBUNNZUUTUNNUOXPYRUNNUVIVCABYRCDEFGHIJKLMUPUQZQUUBURUSZVBXPUUHUUSUUIU
      VAUKXPUUHUUFYLUJZUKOUUSXPUUGUVLUUFUKXPYLUVHVDVEXPUUFYLUVGUVHVBVMXPUVCUVIU
      UIUVAVNUOUVJQUUBVFUSVGXPUUQUUFUUTULOZYLULOUVBXPUUDUVMYLULXPUVDUVIUUDUVMVN
      ZUVFUVJUVCUVDUVIUVNUOQYQUUBVOVHVIVJXPUUFUUTYLUVGUVKUVHVKVMVLXPUUOPYGTOYGX
      PUUNYGPTXMXOUUNYGVNXNXMXOVPZUUMYFSRUVOUULYEGUVOUUKBAFBDEHIKVQVEVRVJVSVEXP
      YGXPYGABCDEFGHIJKLMVTWAZWBVMVGXPUDWCNYDUUPVNXPYCUUOUUJUUPUAWEPUDWCWDWFXQU
      DVNZXRPYBUUNTUVQXRQUDROPXQUDQRWGWHWIZUVQYAUUMSRUVQXTUULGUVQXSUUKAFUVQXRPB
      DUVRVJVEVRVJVGXPXQWCNZVPXRYBUVSXRUNNZXPUVSUVCXQWJNUVTUOXQWKQXQWLUSZWMUVSX
      PUVTYBUNNUWAABXRCDEFGHIJKLMUPWNWOZXPYCUUIUUHUUJUASPWEWCWDWPXQWEVNZXRYRYBU
      UBTUWCXRQWEROYRXQWEQRWGWQWIZUWCYAUUASRUWCXTYTGUWCXSYSAFUWCXRYRBDUWDVJVEVR
      VJVGUWBXPYCUUGUUFUUHUAPPSWCWDWRXQSVNZXRYHYBYLTUWEXRQSROYHXQSQRWGWSWIZUWEY
      AYKSRUWEXTYJGUWEXSYIAFUWEXRYHBDUWFVJVEVRVJVGUWBXPPPUEOYCUAUHUUFVNZPWCNXPP
      WTNUVEUWGXAUVGYCUUFUAPXQPVNZXRQYBYQTUWHXRQPROZQXQPQRWGUVCUWIQVNUOQXBXCWIZ
      UWHYAYPSRUWHXTYOGUWHXSYNAFUWHXRQBDUWJVJVEVRVJVGXDUSXEXFXPUUHXGXHXPUUJXGXH
      XPUUPXGXHXIXPUUEUUDYMUKOUURXPYMUUDXPYGYLUVPUVHVAXPUVCUUCUNNUUDUNNUOXPYQUU
      BUVFUVJVAQUUCURUSZXLXPUUDYLYGUWKUVHUVPXJXKVLVJVM $.

    $( Four times the inner product value ~ ipval3 , useful for simplifying
       certain proofs.  (Contributed by NM, 10-Apr-2007.)
       (New usage is discouraged.) $)
    4ipval2 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
        ( 4 x. ( A P B ) ) = ( ( ( ( N ` ( A G B ) ) ^ 2 ) -
               ( ( N ` ( A G ( -u 1 S B ) ) ) ^ 2 ) ) +
               ( _i x. ( ( ( N ` ( A G ( _i S B ) ) ) ^ 2 ) -
               ( ( N ` ( A G ( -u _i S B ) ) ) ^ 2 ) ) ) ) ) $=
      ( wcel c4 co cmul cfv ci cc cnv w3a c2 cexp cneg cmin caddc ipval2 oveq2d
      c1 cdiv wceq cr simp1 nvgcl nvcl syl2anc recnd sqcld neg1cn nvscl 3adant2
      mp3an2 syld3an3 subcld ax-icn negicn mulcl sylancr addcld cc0 wne divcan2
      4cn 4ne0 mp3an23 syl eqtrd ) EUANZAHNZBHNZUBZOABCPZQPOABFPZGRZUCUDPZAUJUE
      ZBDPZFPZGRZUCUDPZUFPZSASBDPZFPZGRZUCUDPZASUEZBDPZFPZGRZUCUDPZUFPZQPZUGPZO
      UKPZQPZXDWBWCXEOQABCDEFGHIJKLMUHUIWBXDTNZXFXDULZWBWLXCWBWFWKWBWEWBWEWBVSW
      DHNWEUMNVSVTWAUNZABEFHIJUOWDEGHILUPUQURUSWBWJWBWJWBVSWIHNZWJUMNXIVSVTWAWH
      HNZXJVSWAXKVTVSWGTNWAXKUTWGBDEHIKVAVCVBAWHEFHIJUOVDWIEGHILUPUQURUSVEWBSTN
      ZXBTNXCTNVFWBWPXAWBWOWBWOWBVSWNHNZWOUMNXIVSVTWAWMHNZXMVSWAXNVTVSXLWAXNVFS
      BDEHIKVAVCVBAWMEFHIJUOVDWNEGHILUPUQURUSWBWTWBWTWBVSWSHNZWTUMNXIVSVTWAWRHN
      ZXOVSWAXPVTVSWQTNWAXPVGWQBDEHIKVAVCVBAWREFHIJUOVDWSEGHILUPUQURUSVESXBVHVI
      VJXGOTNOVKVLXHVNVOXDOVMVPVQVR $.

    ${
      ipval3.3 $e |- M = ( -v ` U ) $.
      $( Expansion of the inner product value ~ ipval .  (Contributed by NM,
         17-Nov-2007.)  (New usage is discouraged.) $)
      ipval3 $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A P B )
               = ( ( ( ( ( N ` ( A G B ) ) ^ 2 ) -
               ( ( N ` ( A M B ) ) ^ 2 ) ) +
               ( _i x. ( ( ( N ` ( A G ( _i S B ) ) ) ^ 2 ) -
               ( ( N ` ( A M ( _i S B ) ) ) ^ 2 ) ) ) ) / 4 ) ) $=
        ( wcel co c2 cexp ci cnv w3a cfv c1 cneg cmin cmul caddc c4 cdiv ipval2
        nvmval fveq2d oveq1d oveq2d wceq cc ax-icn nvscl mp3an2 syld3an3 neg1cn
        3adant2 wa nvsass mp3anr1 mpanr1 mulm1i oveq1i eqtr3di oveq12d eqtr4d
        eqtrd ) EUAPZAIPZBIPZUBZABCQABFQHUCRSQZAUDUEZBDQFQZHUCZRSQZUFQZTATBDQZF
        QHUCRSQZATUEZBDQZFQZHUCZRSQZUFQZUGQZUHQZUIUJQVRABGQZHUCZRSQZUFQZTWEAWDG
        QZHUCZRSQZUFQZUGQZUHQZUIUJQABCDEFHIJKLMNUKVQXCWMUIUJVQWQWCXBWLUHVQWPWBV
        RUFVQWOWARSVQWNVTHABDEFGIJKLOULUMUNUOVQXAWKTUGVQWTWJWEUFVQWSWIRSVQWRWHH
        VQWRAVSWDDQZFQZWHVNVOVPWDIPZWRXEUPVNVPXFVOVNTUQPZVPXFURTBDEIJLUSUTVCAWD
        DEFGIJKLOULVAVQXDWGAFVNVPXDWGUPVOVNVPVDVSTUGQZBDQZXDWGVNXGVPXIXDUPZURVN
        VSUQPXGVPXJVBVSTBDEIJLVEVFVGXHWFBDTURVHVIVJVCUOVMUMUNUOUOVKUNVL $.
    $}
  $}

  ${
    ipid.1 $e |- X = ( BaseSet ` U ) $.
    ipid.6 $e |- N = ( normCV ` U ) $.
    ipid.7 $e |- P = ( .iOLD ` U ) $.
    $( The inner product of a vector with itself is the square of the vector's
       norm.  Equation I4 of [Ponnusamy] p. 362.  (Contributed by NM,
       1-Feb-2007.)  (New usage is discouraged.) $)
    ipidsq $p |- ( ( U e. NrmCVec /\ A e. X ) ->
                ( A P A ) = ( ( N ` A ) ^ 2 ) ) $=
      ( wcel co cfv c2 cexp c1 ci cmul caddc wceq cc0 cc cnv wa cpv cneg cns c4
      cmin cdiv eqid ipval2 3anidm23 nv2 fveq2d cr cle wbr pm3.2i nvsge0 mp3an2
      2re 0le2 eqtrd oveq1d nvcl recnd cn0 2cn mulexp mp3an13 syl oveq1i eqtrdi
      2nn0 sq2 cn0v nvrinv adantr sq0id oveq12d 4cn sqcld mulcl sylancr subid1d
      nvz0 csqrt 1re neg1rr absreim mp2an ax-icn ax-1cn mulneg2i mulridi negeqi
      eqtri oveq2i fveq2i sqneg ax-mp 3eqtr3i 3eqtr2i negicn addcli nvs 3eqtr4a
      cabs nvdir mp3anr1 mpanr1 nvsid 3eqtr3d oveq2d w3a ipval2lem4 mpan2 it0e0
      subidd addridd eqtr2d wne 4ne0 divcan3 mp3an23 3eqtr2d ) CUAIZAEIZUBZAABJ
      ZAACUCKZJZDKZLMJZANUDZACUEKZJYJJZDKZLMJZUGJZOAOAYOJZYJJZDKZLMJZAOUDZAYOJZ
      YJJZDKZLMJZUGJZPJZQJZUFUHJZUFADKZLMJZPJZUFUHJZUUNYFYGYIUULRAABYOCYJDEFYJU
      IZYOUIZGHUJUKYHUUOUUKUFUHYHUUKUUOSQJUUOYHYSUUOUUJSQYHYSUUOSUGJUUOYHYMUUOY
      RSUGYHYMLUUMPJZLMJZUUOYHYLUUSLMYHYLLAYOJZDKZUUSYHYKUVADAYOCYJEFUUQUURULUM
      YFLUNIZSLUOUPZUBYGUVBUUSRUVCUVDUTVAUQLAYOCDEFUURGURUSVBVCYHUUTLLMJZUUNPJZ
      UUOYHUUMTIZUUTUVFRZYHUUMACDEFGVDVEZLTIUVGLVFIUVHVGVMLUUMLVHVIVJUVEUFUUNPV
      NVKVLVBYHYQYHYQCVOKZDKZSYHYPUVJDAYOCYJEUVJFUUQUURUVJUIZVPUMYFUVKSRYGCDUVJ
      UVLGWEVQVBVRVSYHUUOYHUFTIZUUNTIZUUOTIVTYHUUMUVIWAZUFUUNWBWCZWDVBYHUUJOSPJ
      SYHUUISOPYHUUIUUCUUCUGJSYHUUHUUCUUCUGYHUUGUUBLMYHNUUDQJZAYOJZDKZNOQJZAYOJ
      ZDKZUUGUUBYHUVQXGKZUUMPJZUVTXGKZUUMPJZUVSUWBUWCUWEUUMPUWCNLMJZUWGQJZWFKZN
      ONPJZQJZXGKZUWENOYNPJZQJZXGKZUWGYNLMJZQJZWFKZUWCUWINUNIZYNUNIUWOUWRRWGWHN
      YNWIWJUWNUVQXGUWMUUDNQUWMUWJUDUUDONWKWLWMUWJOOWKWNZWOWPWQWRUWQUWHWFUWPUWG
      UWGQNTIZUWPUWGRWLNWSWTWQWRXAUWSUWSUWLUWIRWGWGNNWIWJUWKUVTXGUWJONQUWTWQWRX
      BVKYFUVQTIYGUVSUWDRNUUDWLXCXDUVQAYOCDEFUURGXEUSYFUVTTIYGUWBUWFRNOWLWKXDUV
      TAYOCDEFUURGXEUSXFYHUVRUUFDYHUVRNAYOJZUUEYJJZUUFYFUUDTIZYGUVRUXCRZXCYFUXA
      UXDYGUXEWLNUUDAYOCYJEFUUQUURXHXIXJYHUXBAUUEYJAYOCEFUURXKZVCVBUMYHUWAUUADY
      HUWAUXBYTYJJZUUAYFOTIZYGUWAUXGRZWKYFUXAUXHYGUXIWLNOAYOCYJEFUUQUURXHXIXJYH
      UXBAYTYJUXFVCVBUMXLVCXMYHUUCYFYGUUCTIZYFYGYGXNUXHUXJWKAAOBYOCYJDEFUUQUURG
      HXOXPUKXRVBXMXQVLVSYHUUOUVPXSXTVCYHUVNUUPUUNRZUVOUVNUVMUFSYAUXKVTYBUUNUFY
      CYDVJYE $.

    $( Norm expressed in terms of inner product.  (Contributed by NM,
       11-Sep-2007.)  (New usage is discouraged.) $)
    ipnm $p |- ( ( U e. NrmCVec /\ A e. X ) ->
                ( N ` A ) = ( sqrt ` ( A P A ) ) ) $=
      ( cnv wcel wa co csqrt cfv c2 cexp ipidsq fveq2d nvcl nvge0 sqrtsqd
      eqtr2d ) CIJAEJKZAABLZMNADNZOPLZMNUEUCUDUFMABCDEFGHQRUCUEACDEFGSACDEFGTUA
      UB $.
  $}

  ${
    $d k A $.  $d k B $.  $d k x y U $.  $d k x y X $.
    ipcl.1 $e |- X = ( BaseSet ` U ) $.
    ipcl.7 $e |- P = ( .iOLD ` U ) $.
    $( An inner product is a complex number.  (Contributed by NM, 1-Feb-2007.)
       (Revised by Mario Carneiro, 5-May-2014.)  (New usage is discouraged.) $)
    dipcl $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                ( A P B ) e. CC ) $=
      ( vk cnv wcel w3a co c1 c4 cfz ci cexp cfv cc eqid cns cpv cnmcv cmul csu
      cv c2 cdiv ipval fzfid cn0 ax-icn elfznn nnnn0d sylancr adantl ipval2lem4
      wa expcl sylan2 mulcld fsumcl cc0 wne 4cn 4ne0 divcl mp3an23 syl eqeltrd
      ) DIJAEJBEJKZABCLMNOLZPHUFZQLZAVNBDUARZLDUBRZLDUCRZRUGQLZUDLZHUEZNUHLZSAB
      CVODHVPVQEFVPTZVOTZVQTZGUIVKVTSJZWASJZVKVLVSHVKMNUJVKVMVLJZURVNVRWGVNSJZV
      KWGPSJVMUKJWHULWGVMVMNUMUNPVMUSUOZUPWGVKWHVRSJWIABVNCVODVPVQEFWBWCWDGUQUT
      VAVBWENSJNVCVDWFVEVFVTNVGVHVIVJ $.

    $( Mapping for the inner product operation.  (Contributed by NM,
       28-Jan-2008.)  (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    ipf $p |- ( U e. NrmCVec -> P : ( X X. X ) --> CC ) $=
      ( vx vy vk cnv wcel cxp cc wf c4 co cv cexp cfv wral eqid c1 cfz ci cnmcv
      cns cpv cmul csu cdiv cmpo w3a ipval dipcl eqeltrrd 3expib ralrimivv fmpo
      c2 sylib dipfval feq1d mpbird ) BIJZCCKZLAMVDLFGCCUANUBOUCHPQOZFPZVEGPZBU
      ERZOBUFRZOBUDRZRURQOUGOHUHNUIOZUJZMZVCVKLJZGCSFCSVMVCVNFGCCVCVFCJZVGCJZVN
      VCVOVPUKVFVGAOVKLVFVGAVHBHVIVJCDVITZVHTZVJTZEULVFVGABCDEUMUNUOUPFGCCVKLVL
      VLTUQUSVCVDLAVLFGAVHBHVIVJCDVQVRVSEUTVAVB $.

    $( The complex conjugate of an inner product reverses its arguments.
       Equation I1 of [Ponnusamy] p. 362.  (Contributed by NM, 1-Feb-2007.)
       (New usage is discouraged.) $)
    dipcj $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
               ( * ` ( A P B ) ) = ( B P A ) ) $=
      ( wcel co cfv c2 cexp cmin ci c4 cdiv wceq cc mpan2 cr cnv w3a ccj cpv c1
      cnmcv cneg cns cmul caddc eqid ipval2 fveq2d 3com23 ipval2lem3 ipval2lem4
      recnd neg1cn subcld ax-icn negicn mulcl sylancr addcld cc0 wne 4ne0 cjdiv
      4cn mp3an23 syl 4re cjre ax-mp oveq2i ipval2lem2 resubcld syl2anc submul2
      cjreim mp3an2 nvcom oveq1d oveq12d negsubdi2d eqcomd oveq2d 3eqtrd eqtrid
      nvdif nvpi eqtrd eqtr4d ) DUAHZAEHZBEHZUBZABCIZUCJABDUDJZIZDUFJZJZKLIZAUE
      UGZBDUHJZIWSIXAJZKLIZMIZNANBXEIWSIXAJZKLIZANUGZBXEIWSIXAJZKLIZMIZUIIZUJIZ
      OPIZUCJZBACIZWQWRXQUCABCXEDWSXAEFWSUKZXEUKZXAUKZGULUMWQXSBAWSIZXAJZKLIZBX
      DAXEIWSIXAJZKLIZMIZNBNAXEIWSIXAJZKLIZBXKAXEIWSIXAJZKLIZMIZUIIZUJIZOPIZXRW
      NWPWOXSYPQBACXEDWSXAEFXTYAYBGULUNWQXRXPUCJZOUCJZPIZYPWQXPRHZXRYSQZWQXHXOW
      QXCXGWQXCABCXEDWSXAEFXTYAYBGUOZUQWQXDRHZXGRHURABXDCXEDWSXAEFXTYAYBGUPSUSZ
      WQNRHZXNRHZXORHUTWQXJXMWQUUEXJRHUTABNCXEDWSXAEFXTYAYBGUPSZWQXKRHZXMRHVAAB
      XKCXEDWSXAEFXTYAYBGUPSZUSZNXNVBVCVDYTORHOVEVFUUAVIVGXPOVHVJVKWQYSYQOPIYPY
      ROYQPOTHYROQVLOVMVNVOWQYQYOOPWQYQXHXOMIZXHNXNUGZUIIZUJIZYOWQXHTHXNTHYQUUK
      QWQXCXGUUBWQUUCXGTHURABXDCXEDWSXAEFXTYAYBGVPSVQWQXJXMWQUUEXJTHUTABNCXEDWS
      XAEFXTYAYBGVPSWQUUHXMTHVAABXKCXEDWSXAEFXTYAYBGVPSVQXHXNVTVRWQXHRHZUUFUUKU
      UNQZUUDUUJUUOUUEUUFUUPUTXHNXNVSWAVRWQXHYHUUMYNUJWQXCYEXGYGMWQXBYDKLWQWTYC
      XAABDWSEFXTWBUMWCWQXFYFKLABXEDWSXAEFXTYAYBWJWCWDWQUULYMNUIWQUULXMXJMIYMWQ
      XJXMUUGUUIWEWQXMYJXJYLMWQXLYIKLWQYIXLWNWPWOYIXLQBAXEDWSXAEFXTYAYBWKUNWFWC
      WQXIYKKLABXEDWSXAEFXTYAYBWKWCWDWLWGWDWHWCWIWLWMWM $.

    $( An inner product times its conjugate.  (Contributed by NM, 23-Nov-2007.)
       (New usage is discouraged.) $)
    ipipcj $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) ->
                ( ( A P B ) x. ( B P A ) ) = ( ( abs ` ( A P B ) ) ^ 2 ) ) $=
      ( cnv wcel w3a co cabs cfv c2 cexp ccj cmul dipcl absvalsqd dipcj oveq2d
      eqtr2d ) DHIAEIBEIJZABCKZLMNOKUDUDPMZQKUDBACKZQKUCUDABCDEFGRSUCUEUFUDQABC
      DEFGTUAUB $.

    $( Orthogonality (meaning inner product is 0) is commutative.  (Contributed
       by NM, 17-Apr-2008.)  (New usage is discouraged.) $)
    diporthcom $p |- ( ( U e. NrmCVec /\ A e. X /\ B e. X )
              -> ( ( A P B ) = 0 <-> ( B P A ) = 0 ) ) $=
      ( cnv wcel co cc0 wceq ccj cfv fveq2 cj0 eqtrdi dipcj eqeq1d imbitrid w3a
      3com23 impbid ) DHIZAEIZBEIZUAZABCJZKLZBACJZKLZUIUHMNZKLUGUKUIULKMNZKUHKM
      OPQUGULUJKABCDEFGRSTUKUJMNZKLUGUIUKUNUMKUJKMOPQUGUNUHKUDUFUEUNUHLBACDEFGR
      UBSTUC $.
  $}

  ${
    dip0r.1 $e |- X = ( BaseSet ` U ) $.
    dip0r.5 $e |- Z = ( 0vec ` U ) $.
    dip0r.7 $e |- P = ( .iOLD ` U ) $.
    $( Inner product with a zero second argument.  (Contributed by NM,
       5-Feb-2007.)  (New usage is discouraged.) $)
    dip0r $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( A P Z ) = 0 ) $=
      ( wcel co cfv c2 cexp cmin ci caddc c4 cc0 wceq oveq2d cnv cpv cnmcv cneg
      wa c1 cns cmul cdiv nvzcl adantr eqid ipval2 mpd3an3 cc neg1cn nvsz mpan2
      fveq2d oveq1d ipval2lem3 recnd subidd negicn ax-icn eqtr4d w3a ipval2lem4
      cr eqtrd oveq12d it0e0 oveq2i 00id eqtri eqtrdi 4cn 4ne0 div0i ) CUAIZADI
      ZUEZAEBJZAECUBKZJZCUCKZKZLMJZAUFUDZECUGKZJZWDJZWFKZLMJZNJZOAOEWJJZWDJZWFK
      ZLMJZAOUDZEWJJZWDJZWFKZLMJZNJZUHJZPJZQUIJZRVTWAEDIZWCXHSVTXIWACDEFGUJUKZA
      EBWJCWDWFDFWDULZWJULZWFULZHUMUNWBXHRQUIJRWBXGRQUIWBXGRORUHJZPJZRWBWORXFXN
      PWBWOWHWHNJRWBWNWHWHNWBWMWGLMWBWLWEWFWBWKEAWDVTWKESZWAVTWIUOIXPUPWIWJCEXL
      GUQURUKTUSUTTWBWHWBWHVTWAXIWHVIIXJAEBWJCWDWFDFXKXLXMHVAUNVBVCVJWBXEROUHWB
      XEWSWSNJRWBXDWSWSNWBXCWRLMWBXBWQWFWBXAWPAWDVTXAWPSWAVTXAEWPVTWTUOIXAESVDW
      TWJCEXLGUQURVTOUOIZWPESVEOWJCEXLGUQURVFUKTUSUTTWBWSVTWAXIWSUOIZXJVTWAXIVG
      XQXRVEAEOBWJCWDWFDFXKXLXMHVHURUNVCVJTVKXORRPJRXNRRPVLVMVNVOVPUTQVQVRVSVPV
      J $.

    $( Inner product with a zero first argument.  Part of proof of Theorem 6.44
       of [Ponnusamy] p. 361.  (Contributed by NM, 5-Feb-2007.)
       (New usage is discouraged.) $)
    dip0l $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( Z P A ) = 0 ) $=
      ( cnv wcel wa co ccj cfv cc0 wceq nvzcl adantr dipcj mpd3an3 dip0r fveq2d
      cj0 eqtrdi eqtr3d ) CIJZADJZKZAEBLZMNZEABLZOUFUGEDJZUJUKPUFULUGCDEFGQRAEB
      CDFHSTUHUJOMNOUHUIOMABCDEFGHUAUBUCUDUE $.

    $( The inner product of a vector with itself is zero iff the vector is
       zero.  Part of Definition 3.1-1 of [Kreyszig] p. 129.  (Contributed by
       NM, 24-Jan-2008.)  (New usage is discouraged.) $)
    ipz $p |- ( ( U e. NrmCVec /\ A e. X ) -> ( ( A P A ) = 0 <-> A = Z ) ) $=
      ( cnv wcel wa co cc0 wceq cnmcv cfv c2 cexp eqid ipidsq eqeq1d cc wb nvcl
      recnd sqeq0 syl nvz 3bitrd ) CIJADJKZAABLZMNACOPZPZQRLZMNZUMMNZAENUJUKUNM
      ABCULDFULSZHTUAUJUMUBJUOUPUCUJUMACULDFUQUDUEUMUFUGACULDEFGUQUHUI $.
  $}

  ${
    $d k x y z J $.  $d k x y z K $.  $d k x y z U $.
    dipcn.p $e |- P = ( .iOLD ` U ) $.
    dipcn.c $e |- C = ( IndMet ` U ) $.
    dipcn.j $e |- J = ( MetOpen ` C ) $.
    dipcn.k $e |- K = ( TopOpen ` CCfld ) $.
    $( Inner product is jointly continuous in both arguments.  (Contributed by
       NM, 21-Aug-2007.)  (Revised by Mario Carneiro, 10-Sep-2015.)
       (New usage is discouraged.) $)
    dipcn $p |- ( U e. NrmCVec -> P e. ( ( J tX J ) Cn K ) ) $=
      ( vx vy vk vz wcel cfv c4 co ccn cc a1i cnv cba c1 cfz ci cv cexp cns cpv
      cnmcv c2 cmul csu cdiv cmpo ctx eqid dipfval ctopon imsxmet mopntopon syl
      cxmet fzfid wa adantr cnfldtopon cn0 ax-icn cn elfznn adantl nnnn0d expcl
      sylancr cnmpt2c cnmpt1st cnmpt2nd smcn cnmpt22f vacn nmcnc cnmpt21f oveq1
      cmpt sqcn cnmpt21 mulcn fsum2cn cc0 wne 4cn 4ne0 divccn mp2an eqeltrd ) C
      UANZBJKCUBOZWRUCPUDQZUELUFZUGQZJUFZXAKUFZCUHOZQZCUIOZQZCUJOZOZUKUGQZULQZL
      UMZPUNQZUODDUPQZERQJKBXDCLXFXHWRWRUQZXFUQZXDUQZXHUQZFURWQJKMXLMUFZPUNQZXM
      DDEEWRWRSWQAWRVCONDWRUSONZACWRXOGUTADWRHVAVBZYBWQJKWSXKLDEDWRWRIYBWQUCPVD
      YBWQWTWSNZVEZJKXAXJULDDEEEWRWRWQYAYCYBVFZYEYDJKXADDEWRWRSYEYEESUSONZYDEIV
      GZTZYDUESNWTVHNXASNVIYDWTYCWTVJNWQWTPVKVLVMUEWTVNVOVPZYDJKMXIXSUKUGQZXJDD
      EEWRWRSYEYEYDJKXGXHDDDEWRWRYEYEYDJKXBXEXFDDDDDWRWRYEYEYDJKDDWRWRYEYEVQYDJ
      KXAXCXDDDEDDWRWRYEYEYIYDJKDDWRWRYEYEVRWQXDEDUPQDRQNYCAXDCDEGHXQIVSVFVTWQX
      FXNDRQNYCACXFDGHXPWAVFVTWQXHDERQNYCACDEXHXRGHIWBVFWCYHMSYJWEEERQZNYDMEIWF
      TXSXIUKUGWDWGULEEUPQERQNYDEIWHTVTWIYFWQYGTMSXTWEYKNZWQPSNPWJWKYLWLWMMPEIW
      NWOTXSXLPUNWDWGWP $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Subspaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c SubSp $.

  $( Extend class notation with the class of all subspaces of normed complex
     vector spaces. $)
  css $a class SubSp $.

  ${
    $d u w $.
    $( Define the class of all subspaces of normed complex vector spaces.
       (Contributed by NM, 26-Jan-2008.)  (New usage is discouraged.) $)
    df-ssp $a |- SubSp = ( u e. NrmCVec |->
     { w e. NrmCVec | ( ( +v ` w ) C_ ( +v ` u ) /\ ( .sOLD ` w ) C_ ( .sOLD `
        u )
         /\ ( normCV ` w ) C_ ( normCV ` u ) ) } ) $.
  $}

  ${
    $d u w G $.  $d u w N $.  $d u w S $.  $d u w U $.
    sspval.g $e |- G = ( +v ` U ) $.
    sspval.s $e |- S = ( .sOLD ` U ) $.
    sspval.n $e |- N = ( normCV ` U ) $.
    sspval.h $e |- H = ( SubSp ` U ) $.
    $( The set of all subspaces of a normed complex vector space.  (Contributed
       by NM, 26-Jan-2008.)  (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    sspval $p |- ( U e. NrmCVec -> H = { w e. NrmCVec | (
         ( +v ` w ) C_ G /\ ( .sOLD ` w ) C_ S /\ ( normCV ` w ) C_ N ) } ) $=
      ( vu cnv wcel cfv cpv wss cns cnmcv fveq2 eqtr4di css cv crab wceq sseq2d
      w3a 3anbi123d rabbidv df-ssp cpw cxp fvexi pwex xpex wi rabss cop wa fvex
      elpw opelxpi syl2anbr biimpri syl2an 3impa eqid nvop eleq1d mprgbir ssexi
      imbitrrid fvmpt eqtrid ) CLMECUANAUBZONZDPZVNQNZBPZVNRNZFPZUFZALUCZJKCVOK
      UBZONZPZVQWCQNZPZVSWCRNZPZUFZALUCWBLUAWCCUDZWJWAALWKWEVPWGVRWIVTWKWDDVOWK
      WDCONDWCCOSGTUEWKWFBVQWKWFCQNBWCCQSHTUEWKWHFVSWKWHCRNFWCCRSITUEUGUHAKUIWB
      DUJZBUJZUKZFUJZUKZWNWOWLWMDDCOGULUMBBCQHULUMUNFFCRIULUMUNWBWPPWAVNWPMZUOA
      LWAALWPUPWAWQVNLMZVOVQUQZVSUQZWPMZVPVRVTXAVPVRURWSWNMZVSWOMZXAVTVPVOWLMVQ
      WMMXBVRVODVNOUSUTVQBVNQUSUTVOVQWLWMVAVBXCVTVSFVNRUSUTVCWSVSWNWOVAVDVEWRVN
      WTWPVQVNVOVSVOVFVQVFVSVFVGVHVKVIVJVLVM $.
  $}

  ${
    $d w F $.  $d w G $.  $d w M $.  $d w N $.  $d w R $.  $d w S $.  $d w U $.
    $d w W $.
    isssp.g $e |- G = ( +v ` U ) $.
    isssp.f $e |- F = ( +v ` W ) $.
    isssp.s $e |- S = ( .sOLD ` U ) $.
    isssp.r $e |- R = ( .sOLD ` W ) $.
    isssp.n $e |- N = ( normCV ` U ) $.
    isssp.m $e |- M = ( normCV ` W ) $.
    isssp.h $e |- H = ( SubSp ` U ) $.
    $( The predicate "is a subspace."  (Contributed by NM, 26-Jan-2008.)
       (New usage is discouraged.) $)
    isssp $p |- ( U e. NrmCVec -> ( W e. H <-> ( W e. NrmCVec /\ (
               F C_ G /\ R C_ S /\ M C_ N ) ) ) ) $=
      ( vw cnv cfv wss wcel cv cpv cns cnmcv crab wa sspval eleq2d wceq eqtr4di
      w3a fveq2 sseq1d 3anbi123d elrab bitrdi ) CRUAZIFUAIQUBZUCSZETZUSUDSZBTZU
      SUESZHTZULZQRUFZUAIRUADETZABTZGHTZULZUGURFVGIQBCEFHJLNPUHUIVFVKQIRUSIUJZV
      AVHVCVIVEVJVLUTDEVLUTIUCSDUSIUCUMKUKUNVLVBABVLVBIUDSAUSIUDUMMUKUNVLVDGHVL
      VDIUESGUSIUEUMOUKUNUOUPUQ $.
  $}

  ${
    sspid.h $e |- H = ( SubSp ` U ) $.
    $( A normed complex vector space is a subspace of itself.  (Contributed by
       NM, 8-Apr-2008.)  (New usage is discouraged.) $)
    sspid $p |- ( U e. NrmCVec -> U e. H ) $=
      ( cnv wcel cpv cfv wss cns cnmcv w3a ssid 3pm3.2i jctr eqid isssp mpbird
      wa ) ADEZABESAFGZTHZAIGZUBHZAJGZUDHZKZRSUFUAUCUETLUBLUDLMNUBUBATTBUDUDATO
      ZUGUBOZUHUDOZUICPQ $.
  $}

  ${
    sspnv.h $e |- H = ( SubSp ` U ) $.
    $( A subspace is a normed complex vector space.  (Contributed by NM,
       27-Jan-2008.)  (New usage is discouraged.) $)
    sspnv $p |- ( ( U e. NrmCVec /\ W e. H ) -> W e. NrmCVec ) $=
      ( cnv wcel cpv cfv wss cns cnmcv w3a eqid isssp simprbda ) AEFCBFCEFCGHZA
      GHZICJHZAJHZICKHZAKHZILRSAPQBTUACQMPMSMRMUAMTMDNO $.
  $}

  ${
    sspba.x $e |- X = ( BaseSet ` U ) $.
    sspba.y $e |- Y = ( BaseSet ` W ) $.
    sspba.h $e |- H = ( SubSp ` U ) $.
    $( The base set of a subspace is included in the parent base set.
       (Contributed by NM, 27-Jan-2008.)  (New usage is discouraged.) $)
    sspba $p |- ( ( U e. NrmCVec /\ W e. H ) -> Y C_ X ) $=
      ( cnv wcel wa cpv cfv crn wss cns cnmcv w3a eqid bafval isssp simp1d rnss
      simplbda syl 3sstr4g ) AIJZCBJZKZCLMZNZALMZNZEDUIUJULOZUKUMOUIUNCPMZAPMZO
      ZCQMZAQMZOZUGUHCIJUNUQUTRUOUPAUJULBURUSCULSZUJSZUPSUOSUSSURSHUAUDUBUJULUC
      UECUJEGVBTAULDFVATUF $.
  $}

  ${
    $d x y F $.  $d x y G $.  $d x y H $.  $d x y U $.  $d x y W $.
    $d x y Y $.
    sspg.y $e |- Y = ( BaseSet ` W ) $.
    sspg.g $e |- G = ( +v ` U ) $.
    sspg.f $e |- F = ( +v ` W ) $.
    sspg.h $e |- H = ( SubSp ` U ) $.
    $( Vector addition on a subspace is a restriction of vector addition on the
       parent space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspg $p |- ( ( U e. NrmCVec /\ W e. H ) -> F = ( G |` ( Y X. Y ) ) ) $=
      ( vx vy wcel wa wceq wfn wss cfv eqid syl cnv cxp cres cv co wral w3a cba
      wfun nvgf ffund funresd adantr wf sspnv ffnd fnresdm cnmcv isssp simplbda
      simp1d ssres eqsstrrd 3jca oprssov sylan eqcomd ralrimivva jctil wb sspba
      cns xpss12 syl2anc fnssres eqfnov mpbird ) AUAMZEDMZNZBCFFUBZUCZOZWAWAOZK
      UDZLUDZBUEZWEWFWBUEZOZLFUFKFUFZNZVTWJWDVTWIKLFFVTWEFMWFFMNZNWHWGVTWBUIZBW
      APZBWBQZUGWLWHWGOVTWMWNWOVRWMVSVRWACVRAUHRZWPUBZWPCACWPWPSZHUJZUKULUMVTWA
      FBVTEUAMZWAFBUNADEJUOEBFGIUJTUPZVTBBWAUCZWBVTWNXBBOXAWABUQTVTBCQZXBWBQVTX
      CEVLRZAVLRZQZEURRZAURRZQZVRVSWTXCXFXIUGXDXEABCDXGXHEHIXESXDSXHSXGSJUSUTVA
      BCWAVBTVCVDWEWFFFWBBVEVFVGVHWASVIVTWNWBWAPZWCWKVJXAVTCWQPZWAWQQZXJVRXKVSV
      RWQWPCWSUPUMVTFWPQZXMXLADEWPFWRGJVKZXNFWPFWPVMVNWQWACVOVNKLFFFFBWBVPVNVQ
      $.

    $( Vector addition on a subspace in terms of vector addition on the parent
       space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspgval $p |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y ) ) ->
                    ( A F B ) = ( A G B ) ) $=
      ( cnv wcel wa co cxp cres sspg oveqd ovres sylan9eq ) CMNGFNOZAHNBHNOABDP
      ABEHHQRZPABEPUCDUDABCDEFGHIJKLSTABHHEUAUB $.
  $}

  ${
    $d x y R $.  $d x y S $.  $d x y H $.  $d x y U $.  $d x y W $.
    $d x y Y $.
    ssps.y $e |- Y = ( BaseSet ` W ) $.
    ssps.s $e |- S = ( .sOLD ` U ) $.
    ssps.r $e |- R = ( .sOLD ` W ) $.
    ssps.h $e |- H = ( SubSp ` U ) $.
    $( Scalar multiplication on a subspace is a restriction of scalar
       multiplication on the parent space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    ssps $p |- ( ( U e. NrmCVec /\ W e. H ) -> R = ( S |` ( CC X. Y ) ) ) $=
      ( vx vy wcel wa cc wceq wfn wss cfv eqid cnv cxp cres cv co wral wfun w3a
      cba nvsf ffund funresd adantr sspnv syl ffnd fnresdm cnmcv isssp simplbda
      cpv simp2d ssres eqsstrrd 3jca oprssov sylan eqcomd ralrimivva jctil ssid
      wf wb sspba xpss12 sylancr fnssres syl2anc eqfnov mpbird ) CUAMZEDMZNZABO
      FUBZUCZPZWDWDPZKUDZLUDZAUEZWHWIWEUEZPZLFUFKOUFZNZWCWMWGWCWLKLOFWCWHOMWIFM
      NZNWKWJWCWEUGZAWDQZAWERZUHWOWKWJPWCWPWQWRWAWPWBWAWDBWAOCUISZUBZWSBBCWSWST
      ZHUJZUKULUMWCWDFAWCEUAMZWDFAVLCDEJUNAEFGIUJUOUPZWCAAWDUCZWEWCWQXEAPXDWDAU
      QUOWCABRZXEWERWCEVASZCVASZRZXFEURSZCURSZRZWAWBXCXIXFXLUHABCXGXHDXJXKEXHTX
      GTHIXKTXJTJUSUTVBABWDVCUOVDVEWHWIOFWEAVFVGVHVIWDTVJWCWQWEWDQZWFWNVMXDWCBW
      TQZWDWTRZXMWAXNWBWAWTWSBXBUPUMWCOORFWSRXOOVKCDEWSFXAGJVNOOFWSVOVPWTWDBVQV
      RKLOFOFAWEVSVRVT $.

    $( Scalar multiplication on a subspace in terms of scalar multiplication on
       the parent space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspsval $p |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. CC /\ B e. Y ) ) ->
                    ( A R B ) = ( A S B ) ) $=
      ( cnv wcel wa cc co cxp cres ssps oveqd ovres sylan9eq ) EMNGFNOZAPNBHNOA
      BCQABDPHRSZQABDQUDCUEABCDEFGHIJKLTUAABPHDUBUC $.
  $}

  $( TODO - sspvallem doesn't save space yet, but might if another
     operation is added. $)
  $(
  @{
    @d x y F @.  @d x y G @.  @d x y H @.  @d x y U @.  @d x y W @.
    @d x y Y @.
    sspvallem.y @e |- Y = ( BaseSet ` W ) @.
    sspvallem.h @e |- H = ( SubSp ` U ) @.
    @{
      sspvallem.1 @e |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y )
         ) -> R = S ) @.
      sspvallem.2 @e |- ( ( W e. NrmCVec /\ A e. Y /\ B e. Y ) -> P = R ) @.
      sspvallem.3 @e |- ( ( U e. NrmCVec /\ A e. ( BaseSet ` U ) /\
          B e. ( BaseSet ` U ) ) -> Q = S ) @.
      @( Lemma for ~ sspmval and others. @)
      sspvallem @p |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y ) )
          -> P = Q ) @=
       ( cnv wcel wa wceq 3expb sspnv sylanOLD cba cfv eqid sspba sseld anim12d
        imp adantlr syldan 3eqtr4d ) GPQZIHQZRZAJQZBJQZRZREFCDMIPQZURCESZUOUSUP
        UQUTNTGHILUAUBUOURAGUCUDZQZBVAQZRZDFSZUOURVDUOUPVBUQVCUOJVAAGHIVAJVAUEK
        LUFZUGUOJVABVFUGUHUIUMVDVEUNUMVBVCVEOTUJUKUL @.
        @( [ ?] @) @( [1-Feb-2008] @)
    @}

    @{
      sspmlem.1  @e |- ( ( ( U e. NrmCVec /\ W e. H ) /\ (
       x e. Y /\ y e. Y ) ) -> ( x F y ) = ( x G y ) ) @.
      sspmlem.2 @e |- ( W e. NrmCVec -> F : ( Y X. Y ) --> R ) @.
      sspmlem.3 @e |- ( U e. NrmCVec -> G : ( ( BaseSet ` U ) X.
               ( BaseSet ` U ) ) --> S ) @.
      @( Lemma for ~ sspm and others. @)
      sspmlem @p |- ( ( U e. NrmCVec /\ W e. H ) ->
            F = ( G |` ( Y X. Y ) ) ) @=
        ( cnv wcel wa cxp cres wceq cv co wral ovres adantl eqtr4d ex
        ralrimivv eqid jctil wfn wb eqfnov wf sspnv ffn 3syl cba cfv wss
   fnssres syl adantr sspba xpss12 anidms sylancOLD mpbird ) EPQZIHQZRZFGJJSZTZ
        UAZVMVMUAZAUBZBUBZFUCZVQVRVNUCZUAZBJUDAJUDZRZVLWBVPVLWAABJJVLVQJQVRJQRZ
        WAVLWDRVSVQVRGUCZVTMWDVTWEUAVLVQVRJJGUEUFUGUHUIVMUJUKFVMULZVNVMULZVOWCU
        MVLABJJJJFVNUNVLIPQVMCFUOWFEHILUPNVMCFUQURGEUSUTZWHSZULZVMWIVAZWGVLWIVM
        GVBVJWJVKVJWIDGUOWJOWIDGUQVCVDVLJWHVAZWKEHIWHJWHUJKLVEWLWKJWHJWHVFVGVCV
        HVHVI @.
        @( [ ?] @) @( [1-Feb-2008] @)
    @}
  @}
  $)

  ${
    $d x y F $.  $d x y G $.  $d x y H $.  $d x y U $.  $d x y W $.
    $d x y Y $.
    sspmlem.y $e |- Y = ( BaseSet ` W ) $.
    sspmlem.h $e |- H = ( SubSp ` U ) $.
    sspmlem.1 $e |- ( ( ( U e. NrmCVec /\ W e. H ) /\ (
             x e. Y /\ y e. Y ) ) -> ( x F y ) = ( x G y ) ) $.
    sspmlem.2 $e |- ( W e. NrmCVec -> F : ( Y X. Y ) --> R ) $.
    sspmlem.3 $e |- ( U e. NrmCVec -> G : ( ( BaseSet ` U ) X.
             ( BaseSet ` U ) ) --> S ) $.
    $( Lemma for ~ sspm and others.  (Contributed by NM, 1-Feb-2008.)
       (New usage is discouraged.) $)
    sspmlem $p |- ( ( U e. NrmCVec /\ W e. H ) -> F = ( G |` ( Y X. Y ) ) ) $=
      ( wcel wa wceq co wfn cnv cxp cres cv wral ovres adantl eqtr4d ralrimivva
      eqid jctil wb sspnv ffn 3syl cba cfv wss ffnd adantr sspba xpss12 syl2anc
      wf fnssres eqfnov mpbird ) EUAPZIHPZQZFGJJUBZUCZRZVKVKRZAUDZBUDZFSZVOVPVL
      SZRZBJUEAJUEZQZVJVTVNVJVSABJJVJVOJPVPJPQZQVQVOVPGSZVRMWBVRWCRVJVOVPJJGUFU
      GUHUIVKUJUKVJFVKTZVLVKTZVMWAULVJIUAPVKCFVDWDEHILUMNVKCFUNUOVJGEUPUQZWFUBZ
      TZVKWGURZWEVHWHVIVHWGDGOUSUTVJJWFURZWJWIEHIWFJWFUJKLVAZWKJWFJWFVBVCWGVKGV
      EVCABJJJJFVLVFVCVG $.
  $}

  ${
    $d x y L $.  $d x y M $.  $d x y H $.  $d x y U $.  $d x y W $.
    $d x y Y $.
    sspm.y $e |- Y = ( BaseSet ` W ) $.
    sspm.m $e |- M = ( -v ` U ) $.
    sspm.l $e |- L = ( -v ` W ) $.
    sspm.h $e |- H = ( SubSp ` U ) $.
    $( Vector addition on a subspace in terms of vector addition on the parent
       space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspmval $p |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y ) ) ->
                    ( A L B ) = ( A M B ) ) $=
      ( cnv wcel wa cns cfv co wceq eqid c1 cpv wi sspnv cc neg1cn nvscl mp3an2
      cneg ex syl anim2d imp sspgval syldan sspsval mpanr1 adantrl oveq2d eqtrd
      nvmval 3expb sylan cba sspba sseld anim12d adantlr 3eqtr4d ) CMNZGDNZOZAH
      NZBHNZOZOZAUAUIZBGPQZRZGUBQZRZAVQBCPQZRZCUBQZRZABERZABFRZVPWAAVSWDRZWEVLV
      OVMVSHNZOZWAWHSVLVOWJVLVNWIVMVLGMNZVNWIUCCDGLUDZWKVNWIWKVQUENZVNWIUFVQBVR
      GHIVRTZUGUHUJUKULUMAVSCVTWDDGHIWDTZVTTZLUNUOVPVSWCAWDVLVNVSWCSZVMVLWMVNWQ
      UFVQBVRWBCDGHIWBTZWNLUPUQURUSUTVLWKVOWFWASZWLWKVMVNWSABVRGVTEHIWPWNKVAVBV
      CVLVOACVDQZNZBWTNZOZWGWESZVLVOXCVLVMXAVNXBVLHWTACDGWTHWTTZILVEZVFVLHWTBXF
      VFVGUMVJXCXDVKVJXAXBXDABWBCWDFWTXEWOWRJVAVBVHUOVI $.

    $( Vector subtraction on a subspace is a restriction of vector subtraction
       on the parent space.  (Contributed by NM, 28-Jan-2008.)
       (New usage is discouraged.) $)
    sspm $p |- ( ( U e. NrmCVec /\ W e. H ) -> L = ( M |` ( Y X. Y ) ) ) $=
      ( vx vy cba cfv cv sspmval nvmf eqid sspmlem ) KLFAMNZACDBEFGJKOLOABCDEFG
      HIJPECFGIQADTTRHQS $.
  $}

  ${
    sspz.z $e |- Z = ( 0vec ` U ) $.
    sspz.q $e |- Q = ( 0vec ` W ) $.
    sspz.h $e |- H = ( SubSp ` U ) $.
    $( The zero vector of a subspace is the same as the parent's.  (Contributed
       by NM, 28-Jan-2008.)  (New usage is discouraged.) $)
    sspz $p |- ( ( U e. NrmCVec /\ W e. H ) -> Q = Z ) $=
      ( cnv wcel wa cnsb cfv co cba wceq sspnv eqid syl nvmid nvzcl jca sspmval
      mpdan syl2anc2 sspba sseldd syldan 3eqtr3d ) BIJZDCJZKZAADLMZNZAABLMZNZAE
      ULADOMZJZURKZUNUPPULDIJZUSBCDHQZUTURURDUQAUQRZGUAZVCUBSAABCUMUODUQVBUORZU
      MRZHUCUDULUTURUNAPVAVCADUMUQAVBVEGTUEUJUKABOMZJUPEPULUQVFABCDVFUQVFRZVBHU
      FULUTURVAVCSUGABUOVFEVGVDFTUHUI $.
  $}

  ${
    $d x H $.  $d x M $.  $d x N $.  $d x U $.  $d x W $.  $d x Y $.
    sspn.y $e |- Y = ( BaseSet ` W ) $.
    sspn.n $e |- N = ( normCV ` U ) $.
    sspn.m $e |- M = ( normCV ` W ) $.
    sspn.h $e |- H = ( SubSp ` U ) $.
    $( The norm on a subspace is a restriction of the norm on the parent space.
       (Contributed by NM, 28-Jan-2008.)  (New usage is discouraged.) $)
    sspn $p |- ( ( U e. NrmCVec /\ W e. H ) -> M = ( N |` Y ) ) $=
      ( vx cnv wcel wa cr syl cfv wfn wss eqid cres wf sspnv nvf ffnd cba sspba
      adantr fnssres syl2anc cv wfun cdm ffund funresd ad2antrr fnresdm cpv cns
      wceq w3a isssp simplbda simp3d ssres eqsstrrd fdmd eleq2d biimpar funssfv
      sylan syl3anc eqcomd eqfnfvd ) ALMZEBMZNZKFCDFUAZVQFOCVQELMZFOCUBABEJUCZE
      CFGIUDZPUEZVQDAUFQZRZFWCSVRFRVOWDVPVOWCODADWCWCTZHUDZUEUHABEWCFWEGJUGWCFD
      UIUJVQKUKZFMZNZWGVRQZWGCQZWIVRULZCVRSZWGCUMZMZWJWKUTVOWLVPWHVOFDVOWCODWFU
      NUOUPVQWMWHVQCCFUAZVRVQCFRWPCUTWBFCUQPVQCDSZWPVRSVQEURQZAURQZSZEUSQZAUSQZ
      SZWQVOVPVSWTXCWQVAXAXBAWRWSBCDEWSTWRTXBTXATHIJVBVCVDCDFVEPVFUHVQVSWHWOVTV
      SWOWHVSWNFWGVSFOCWAVGVHVIVKWGVRCVJVLVMVN $.

    $( The norm on a subspace in terms of the norm on the parent space.
       (Contributed by NM, 28-Jan-2008.)  (New usage is discouraged.) $)
    sspnval $p |- ( ( U e. NrmCVec /\ W e. H /\ A e. Y ) ->
                    ( M ` A ) = ( N ` A ) ) $=
      ( cnv wcel cfv wceq wa cres sspn fveq1d fvres sylan9eq 3impa ) BLMZFCMZAG
      MZADNZAENZOUCUDPZUEUFAEGQZNUGUHADUIBCDEFGHIJKRSAGETUAUB $.
  $}

  ${
    sspims.y $e |- Y = ( BaseSet ` W ) $.
    sspims.d $e |- D = ( IndMet ` U ) $.
    sspims.c $e |- C = ( IndMet ` W ) $.
    sspims.h $e |- H = ( SubSp ` U ) $.
    $d x y C $.  $d x y D $.  $d x y H $.  $d x y U $.  $d x y W $.
    $d x y Y $.
    $( The induced metric on a subspace in terms of the induced metric on the
       parent space.  (Contributed by NM, 1-Feb-2008.)
       (New usage is discouraged.) $)
    sspimsval $p |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y ) ) ->
                    ( A C B ) = ( A D B ) ) $=
      ( cnv wcel wa cfv co wceq eqid 3expb cnsb cnmcv sspnv nvmcl sylan sspnval
      3expa syldan sspmval fveq2d eqtrd imsdval cba sspba sseld anim12d adantlr
      imp 3eqtr4d ) EMNZGFNZOZAHNZBHNZOZOZABGUAPZQZGUBPZPZABEUAPZQZEUBPZPZABCQZ
      ABDQZVFVJVHVMPZVNVBVEVHHNZVJVQRZVBGMNZVEVREFGLUCZVTVCVDVRABGVGHIVGSZUDTUE
      UTVAVRVSVHEFVIVMGHIVMSZVISZLUFUGUHVFVHVLVMABEFVGVKGHIVKSZWBLUIUJUKVBVTVEV
      OVJRZWAVTVCVDWFABCGVGVIHIWBWDKULTUEVBVEAEUMPZNZBWGNZOZVPVNRZVBVEWJVBVCWHV
      DWIVBHWGAEFGWGHWGSZILUNZUOVBHWGBWMUOUPURUTWJWKVAUTWHWIWKABDEVKVMWGWLWEWCJ
      ULTUQUHUS $.

    $( The induced metric on a subspace is a restriction of the induced metric
       on the parent space.  (Contributed by NM, 1-Feb-2008.)
       (New usage is discouraged.) $)
    sspims $p |- ( ( U e. NrmCVec /\ W e. H ) -> C = ( D |` ( Y X. Y ) ) ) $=
      ( vx vy cr cv sspimsval imsdf cba cfv eqid sspmlem ) KLMMCABDEFGJKNLNABCD
      EFGHIJOAEFGIPBCCQRZUASHPT $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Operators on complex vector spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definitions and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c LnOp $.
  $c normOpOLD $.
  $c BLnOp $.
  $c 0op $.

  $( Extend class notation with the class of linear operators on normed complex
     vector spaces. $)
  clno $a class LnOp $.

  $( Extend class notation with the class of operator norms on normed complex
     vector spaces. $)
  cnmoo $a class normOpOLD $.

  $( Extend class notation with the class of bounded linear operators on normed
     complex vector spaces. $)
  cblo $a class BLnOp $.

  $( Extend class notation with the class of zero operators on normed complex
     vector spaces. $)
  c0o $a class 0op $.

  ${
    $d t u w x y z $.
    $( Define the class of linear operators between two normed complex vector
       spaces.  In the literature, an operator may be a partial function, i.e.,
       the domain of an operator is not necessarily the entire vector space.
       However, since the domain of a linear operator is a vector subspace, we
       define it with a complete function for convenience and will use subset
       relations to specify the partial function case.  (Contributed by NM,
       6-Nov-2007.)  (New usage is discouraged.) $)
    df-lno $a |- LnOp = ( u e. NrmCVec , w e. NrmCVec |->
    { t e. ( ( BaseSet ` w ) ^m ( BaseSet ` u ) ) |
       A. x e. CC A. y e. ( BaseSet ` u ) A. z e. ( BaseSet ` u )
      ( t ` ( ( x ( .sOLD ` u ) y ) ( +v ` u ) z ) ) =
         ( ( x ( .sOLD ` w ) ( t ` y ) ) ( +v ` w ) ( t ` z ) ) } ) $.

    $( Define the norm of an operator between two normed complex vector spaces.
       This definition produces an operator norm function for each pair of
       vector spaces ` <. u , w >. ` .  Based on definition of linear operator
       norm in [AkhiezerGlazman] p. 39, although we define it for all operators
       for convenience.  It isn't necessarily meaningful for nonlinear
       operators, since it doesn't take into account operator values at vectors
       with norm greater than 1.  See Equation 2 of [Kreyszig] p. 92 for a
       definition that does (although it ignores the value at the zero vector).
       However, operator norms are rarely if ever used for nonlinear operators.
       (Contributed by NM, 6-Nov-2007.)  (New usage is discouraged.) $)
    df-nmoo $a |- normOpOLD = ( u e. NrmCVec , w e. NrmCVec |->
                ( t e. ( ( BaseSet ` w ) ^m ( BaseSet ` u ) ) |->
        sup ( { x | E. z e. ( BaseSet ` u ) ( ( ( normCV ` u ) ` z ) <_ 1 /\
            x = ( ( normCV ` w ) ` ( t ` z ) ) ) } , RR* , < ) ) ) $.

    $( Define the class of bounded linear operators between two normed complex
       vector spaces.  (Contributed by NM, 6-Nov-2007.)
       (New usage is discouraged.) $)
    df-blo $a |- BLnOp = ( u e. NrmCVec , w e. NrmCVec |->
      { t e. ( u LnOp w ) | ( ( u normOpOLD w ) ` t ) < +oo } ) $.

    $( Define the zero operator between two normed complex vector spaces.
       (Contributed by NM, 28-Nov-2007.)  (New usage is discouraged.) $)
    df-0o $a |- 0op = ( u e. NrmCVec , w e. NrmCVec |->
                        ( ( BaseSet ` u ) X. { ( 0vec ` w ) } ) ) $.
  $}

  $c adj $.
  $( Adjoint of an operator. $)
  caj $a class adj $.

  $c HmOp $.
  $( Set of Hermitional (self-adjoint) operators. $)
  chmo $a class HmOp $.

  ${
    $d s t u w x y $.
    $( Define the adjoint of an operator (if it exists).  The domain of
       ` U adj W ` is the set of all operators from ` U ` to ` W ` that have an
       adjoint.  Definition 3.9-1 of [Kreyszig] p. 196, although we don't
       require that ` U ` and ` W ` be Hilbert spaces nor that the operators be
       linear.  Although we define it for any normed vector space for
       convenience, the definition is meaningful only for inner product spaces.
       (Contributed by NM, 25-Jan-2008.)  (New usage is discouraged.) $)
    df-aj $a |- adj = ( u e. NrmCVec , w e. NrmCVec |->
        { <. t , s >. | ( t : ( BaseSet ` u ) --> ( BaseSet ` w ) /\
                          s : ( BaseSet ` w ) --> ( BaseSet ` u ) /\
        A. x e. ( BaseSet ` u ) A. y e. ( BaseSet ` w )
          ( ( t ` x ) ( .iOLD ` w ) y ) = ( x ( .iOLD ` u ) ( s ` y ) ) ) } )
        $.

    $( Define the set of Hermitian (self-adjoint) operators on a normed complex
       vector space (normally a Hilbert space).  Although we define it for any
       normed vector space for convenience, the definition is meaningful only
       for inner product spaces.  (Contributed by NM, 26-Jan-2008.)
       (New usage is discouraged.) $)
    df-hmo $a |- HmOp = ( u e. NrmCVec |->
                { t e. dom ( u adj u ) | ( ( u adj u ) ` t ) = t } ) $.

$(
    @( Alternate definition of the set of Hermitian (self-adjoint) operators on
       a normed complex vector space (normally a Hilbert space). @)
    dfhm2 @p |- HmOp = { <. u , o >. | ( u e. NrmCVec /\ o = { t | ( t :
  ( BaseSet ` u ) --> ( BaseSet ` u ) /\ A. x e. ( BaseSet ` u ) A. y e.
  ( BaseSet ` u ) ( x ( .iOLD ` u ) ( t ` y ) ) = ( ( t ` x ) ( .iOLD ` u ) y )
       ) } ) } @=
      (  ) ? @.
      @( [ ?] @) @( [8-Feb-2008] @)
$)
  $}

  ${
    $d t u w x y z U $.  $d t u w x y z W $.  $d t u w y z X $.  $d t u w Y $.
    $d t u w G $.  $d t u w R $.  $d t u w H $.  $d t u w S $.
    $d t u w x y z T $.
    lnoval.1 $e |- X = ( BaseSet ` U ) $.
    lnoval.2 $e |- Y = ( BaseSet ` W ) $.
    lnoval.3 $e |- G = ( +v ` U ) $.
    lnoval.4 $e |- H = ( +v ` W ) $.
    lnoval.5 $e |- R = ( .sOLD ` U ) $.
    lnoval.6 $e |- S = ( .sOLD ` W ) $.
    lnoval.7 $e |- L = ( U LnOp W ) $.
    $( The set of linear operators between two normed complex vector spaces.
       (Contributed by NM, 6-Nov-2007.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    lnoval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> L =
      { t e. ( Y ^m X ) | A. x e. CC A. y e. X A. z e. X
        ( t ` ( ( x R y ) G z ) ) = ( ( x S ( t ` y ) ) H ( t ` z ) ) } ) $=
      ( vu vw cnv wcel wa clno co cv cfv wceq wral cc cmap crab cns cpv eqtr4di
      cba fveq2 oveq2d oveqd eqidd oveq123d fveqeq2d raleqbidv rabeqbidv oveq1d
      ralbidv eqeq2d 2ralbidv df-lno ovex rabex ovmpo eqtrid ) GUCUDKUCUDUEJGKU
      FUGAUHZBUHZEUGZCUHZHUGZDUHZUIZVPVQWAUIZFUGZVSWAUIZIUGZUJZCLUKBLUKZAULUKZD
      MLUMUGZUNZTUAUBGKUCUCVPVQUAUHZUOUIZUGZVSWLUPUIZUGZWAUIVPWCUBUHZUOUIZUGZWE
      WQUPUIZUGZUJZCWLURUIZUKZBXCUKZAULUKZDWQURUIZXCUMUGZUNWKUFWBXAUJZCLUKZBLUK
      ZAULUKZDXGLUMUGZUNWLGUJZXFXLDXHXMXNXCLXGUMXNXCGURUILWLGURUSNUQZUTXNXEXKAU
      LXNXDXJBXCLXOXNXBXICXCLXOXNWPVTXAWAXNWNVRVSVSWOHXNWOGUPUIHWLGUPUSPUQXNWME
      VPVQXNWMGUOUIEWLGUOUSRUQVAXNVSVBVCVDVEVEVHVFWQKUJZXLWIDXMWJXPXGMLUMXPXGKU
      RUIMWQKURUSOUQVGXPXKWHAULXPXIWGBCLLXPXAWFWBXPWSWDWEWEWTIXPWTKUPUIIWQKUPUS
      QUQXPWRFVPWCXPWRKUOUIFWQKUOUSSUQVAXPWEVBVCVIVJVHVFABCUBUADVKWIDWJMLUMVLVM
      VNVO $.

    $( The predicate "is a linear operator."  (Contributed by NM, 4-Dec-2007.)
       (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    islno $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> ( T e. L <->
      ( T : X --> Y /\ A. x e. CC A. y e. X A. z e. X
      ( T ` ( ( x R y ) G z ) ) = ( ( x S ( T ` y ) ) H ( T ` z ) ) ) ) ) $=
      ( vw cnv wcel wa cv co cfv wceq wral cc cmap crab wf lnoval eleq2d oveq2d
      fveq1 oveq12d eqeq12d 2ralbidv ralbidv elrab cba fvexi elmap anbi1i bitri
      bitrdi ) GUBUCKUBUCUDZFJUCFAUEZBUEZDUFCUEZHUFZUAUEZUGZVJVKVNUGZEUFZVLVNUG
      ZIUFZUHZCLUIBLUIZAUJUIZUAMLUKUFZULZUCZLMFUMZVMFUGZVJVKFUGZEUFZVLFUGZIUFZU
      HZCLUIBLUIZAUJUIZUDZVIJWDFABCUADEGHIJKLMNOPQRSTUNUOWEFWCUCZWNUDWOWBWNUAFW
      CVNFUHZWAWMAUJWQVTWLBCLLWQVOWGVSWKVMVNFUQWQVQWIVRWJIWQVPWHVJEVKVNFUQUPVLV
      NFUQURUSUTVAVBWPWFWNMLFMKVCOVDLGVCNVDVEVFVGVH $.

    $d t u w A $.  $d t w B $.  $d t C $.
    $( Basic linearity property of a linear operator.  (Contributed by NM,
       4-Dec-2007.)  (Revised by Mario Carneiro, 16-Nov-2013.)
       (New usage is discouraged.) $)
    lnolin $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\
       ( A e. CC /\ B e. X /\ C e. X ) ) ->
      ( T ` ( ( A R B ) G C ) ) = ( ( A S ( T ` B ) ) H ( T ` C ) ) ) $=
      ( vu vw vt cnv wcel w3a cv co cfv wceq wral cc wf wa islno biimp3a simprd
      oveq1 fvoveq1d oveq1d eqeq12d oveq2 fveq2 oveq2d fveq2d rspc3v mpan9 ) GU
      DUEZKUDUEZFJUEZUFZUAUGZUBUGZDUHZUCUGZHUHFUIZVLVMFUIZEUHZVOFUIZIUHZUJZUCLU
      KUBLUKUAULUKZAULUEBLUECLUEUFABDUHZCHUHZFUIZABFUIZEUHZCFUIZIUHZUJZVKLMFUMZ
      WBVHVIVJWKWBUNUAUBUCDEFGHIJKLMNOPQRSTUOUPUQWAWJAVMDUHZVOHUHFUIZAVQEUHZVSI
      UHZUJWCVOHUHZFUIZWGVSIUHZUJUAUBUCABCULLLVLAUJZVPWMVTWOWSVNWLVOFHVLAVMDURU
      SWSVRWNVSIVLAVQEURUTVAVMBUJZWMWQWOWRWTWLWCVOFHVMBADVBUSWTWNWGVSIWTVQWFAEV
      MBFVCVDUTVAVOCUJZWQWEWRWIXAWPWDFVOCWCHVBVEXAVSWHWGIVOCFVCVDVAVFVG $.
  $}

  ${
    $d x y z T $.  $d x y z U $.  $d x y z W $.  $d x y z X $.
    lnof.1 $e |- X = ( BaseSet ` U ) $.
    lnof.2 $e |- Y = ( BaseSet ` W ) $.
    lnof.7 $e |- L = ( U LnOp W ) $.
    $( A linear operator is a mapping.  (Contributed by NM, 4-Dec-2007.)
       (Revised by Mario Carneiro, 18-Nov-2013.)
       (New usage is discouraged.) $)
    lnof $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) -> T : X --> Y ) $=
      ( vx vy vz cnv wcel cv cns cfv co wral eqid wf wa cpv wceq islno simprbda
      cc 3impa ) BMNZDMNZACNZEFAUAZUIUJUBUKULJOZKOZBPQZRLOZBUCQZRAQUMUNAQDPQZRU
      PAQDUCQZRUDLESKESJUGSJKLUOURABUQUSCDEFGHUQTUSTUOTURTIUEUFUH $.
  $}

  ${
    lno0.1 $e |- X = ( BaseSet ` U ) $.
    lno0.2 $e |- Y = ( BaseSet ` W ) $.
    lno0.5 $e |- Q = ( 0vec ` U ) $.
    lno0.z $e |- Z = ( 0vec ` W ) $.
    lno0.7 $e |- L = ( U LnOp W ) $.
    $( The value of a linear operator at zero is zero.  (Contributed by NM,
       4-Dec-2007.)  (Revised by Mario Carneiro, 18-Nov-2013.)
       (New usage is discouraged.) $)
    lno0 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L )
         -> ( T ` Q ) = Z ) $=
      ( cnv wcel w3a cfv co wceq eqid c1 cneg cns cpv neg1cn a1i nvzcl 3ad2ant1
      cc 3jca lnolin mpdan nvlinv fveq2d simp2 lnof ffvelcdmd syl2anc 3eqtr3d )
      CNOZENOZBDOZPZUAUBZACUCQZRACUDQZRZBQZVDABQZEUCQZRVIEUDQZRZVIHVCVDUIOZAFOZ
      VNPVHVLSVCVMVNVNVMVCUEUFUTVAVNVBCFAIKUGZUHZVPUJVDAAVEVJBCVFVKDEFGIJVFTZVK
      TZVETZVJTZMUKULUTVAVHVISVBUTVGABUTVNVGASVOAVECVFFAIVQVSKUMULUNUHVCVAVIGOV
      LHSUTVAVBUOVCFGABBCDEFGIJMUPVPUQVIVJEVKGHJVRVTLUMURUS $.
  $}

  ${
    $d x y z S $.  $d x y z T $.  $d x y z U $.  $d x y z X $.
    lnocoi.l $e |- L = ( U LnOp W ) $.
    lnocoi.m $e |- M = ( W LnOp X ) $.
    lnocoi.n $e |- N = ( U LnOp X ) $.
    lnocoi.u $e |- U e. NrmCVec $.
    lnocoi.w $e |- W e. NrmCVec $.
    lnocoi.x $e |- X e. NrmCVec $.
    lnocoi.s $e |- S e. L $.
    lnocoi.t $e |- T e. M $.
    $( The composition of two linear operators is linear.  (Contributed by NM,
       12-Jan-2008.)  (Revised by Mario Carneiro, 19-Nov-2013.)
       (New usage is discouraged.) $)
    lnocoi $p |- ( T o. S ) e. N $=
      ( wcel cfv co eqid vx vy vz ccom cba wf cv cns cpv wceq wral cc cnv mp3an
      lnof fco mp2an w3a nvscl mp3an1 nvgcl stoic3 sylancr id ffvelcdmi 3pm3.2i
      fvco3 lnolin mpan syl3an fveq2d simp2 oveq2d simp3 oveq12d 3eqtr4rd rgen3
      eqtr4d wa wb islno mpbir2an ) BAUDZFQZCUERZHUERZWCUFZUAUGZUBUGZCUHRZSZUCU
      GZCUIRZSZWCRZWHWIWCRZHUHRZSZWLWCRZHUIRZSZUJZUCWEUKUBWEUKUAULUKZGUERZWFBUF
      ZWEXDAUFZWGGUMQZHUMQZBEQZXEMNPBGEHXDWFXDTZWFTZJUOUNCUMQZXGADQZXFLMOACDGWE
      XDWETZXJIUOUNZWEXDWFBAUPUQXBUAUBUCULWEWEWHULQZWIWEQZWLWEQZURZWOWNARZBRZXA
      XSXFWNWEQZWOYAUJXOXPXQWKWEQZXRYBXLXPXQYCLWHWIWJCWEXNWJTZUSUTXLYCXRYBLWKWL
      CWMWEXNWMTZVAUTVBWEXDWNBAVGVCXSWHWIARZGUHRZSWLARZGUIRZSZBRZWHYFBRZWQSZYHB
      RZWTSZYAXAXPXPXQYFXDQZXRYHXDQZYKYOUJZXPVDWEXDWIAXOVEWEXDWLAXOVEXGXHXIURXP
      YPYQURYRXGXHXIMNPVFWHYFYHYGWQBGYIWTEHXDWFXJXKYITZWTTZYGTZWQTZJVHVIVJXSXTY
      JBXLXGXMURXSXTYJUJXLXGXMLMOVFWHWIWLWJYGACWMYIDGWEXDXNXJYEYSYDUUAIVHVIVKXS
      WRYMWSYNWTXSWPYLWHWQXSXFXQWPYLUJXOXPXQXRVLWEXDWIBAVGVCVMXSXFXRWSYNUJXOXPX
      QXRVNWEXDWLBAVGVCVOVPVRVQXLXHWDWGXCVSVTLNUAUBUCWJWQWCCWMWTFHWEWFXNXKYEYTY
      DUUBKWAUQWB $.
  $}

  ${
    lnoadd.1 $e |- X = ( BaseSet ` U ) $.
    lnoadd.5 $e |- G = ( +v ` U ) $.
    lnoadd.6 $e |- H = ( +v ` W ) $.
    lnoadd.7 $e |- L = ( U LnOp W ) $.
    $( Addition property of a linear operator.  (Contributed by NM,
       7-Dec-2007.)  (Revised by Mario Carneiro, 19-Nov-2013.)
       (New usage is discouraged.) $)
    lnoadd $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\
  ( A e. X /\ B e. X ) ) -> ( T ` ( A G B ) ) = ( ( T ` A ) H ( T ` B ) ) ) $=
      ( cnv wcel c1 cfv co wceq eqid w3a wa cns ax-1cn cba lnolin mp3anr1 simp1
      cc simpl nvsid syl2an fvoveq1d simpl2 wf ffvelcdm syl2anc oveq1d 3eqtr3d
      lnof ) DNOZHNOZCGOZUAZAIOZBIOZUBZUBZPADUCQZRZBERCQZPACQZHUCQZRZBCQZFRZABE
      RCQVLVOFRVDPUIOVEVFVKVPSUDPABVIVMCDEFGHIHUEQZJVQTZKLVITZVMTZMUFUGVHVJABCE
      VDVAVEVJASVGVAVBVCUHVEVFUJZAVIDIJVSUKULUMVHVNVLVOFVHVBVLVQOZVNVLSVAVBVCVG
      UNVDIVQCUOVEWBVGCDGHIVQJVRMUTWAIVQACUPULVLVMHVQVRVTUKUQURUS $.
  $}

  ${
    lnosub.1 $e |- X = ( BaseSet ` U ) $.
    lnosub.5 $e |- M = ( -v ` U ) $.
    lnosub.6 $e |- N = ( -v ` W ) $.
    lnosub.7 $e |- L = ( U LnOp W ) $.
    $( Subtraction property of a linear operator.  (Contributed by NM,
       7-Dec-2007.)  (Revised by Mario Carneiro, 19-Nov-2013.)
       (New usage is discouraged.) $)
    lnosub $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\
  ( A e. X /\ B e. X ) ) -> ( T ` ( A M B ) ) = ( ( T ` A ) N ( T ` B ) ) ) $=
      ( cnv wcel wa cfv co wceq eqid w3a cneg cns cpv neg1cn cba lnolin mp3anr1
      c1 cc ancom2s nvmval2 3expb 3ad2antl1 fveq2d simpl2 simpl ffvelcdm syl2an
      wf lnof simpr syl3anc 3eqtr4d ) DNOZHNOZCEOZUAZAIOZBIOZPZPZUIUBZBDUCQZRAD
      UDQZRZCQZVMBCQZHUCQZRACQZHUDQZRZABFRZCQVTVRGRZVHVJVIVQWBSZVHVMUJOVJVIWEUE
      VMBAVNVSCDVOWAEHIHUFQZJWFTZVOTZWATZVNTZVSTZMUGUHUKVLWCVPCVEVFVKWCVPSZVGVE
      VIVJWLABVNDVOFIJWHWJKULUMUNUOVLVFVTWFOZVRWFOZWDWBSVEVFVGVKUPVHIWFCUTZVIWM
      VKCDEHIWFJWGMVAZVIVJUQIWFACURUSVHWOVJWNVKWPVIVJVBIWFBCURUSVTVRVSHWAGWFWGW
      IWKLULVCVD $.
  $}

  ${
    lnomul.1 $e |- X = ( BaseSet ` U ) $.
    lnomul.5 $e |- R = ( .sOLD ` U ) $.
    lnomul.6 $e |- S = ( .sOLD ` W ) $.
    lnomul.7 $e |- L = ( U LnOp W ) $.
    $( Scalar multiplication property of a linear operator.  (Contributed by
       NM, 5-Dec-2007.)  (Revised by Mario Carneiro, 19-Nov-2013.)
       (New usage is discouraged.) $)
    lnomul $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\
       ( A e. CC /\ B e. X ) ) -> ( T ` ( A R B ) ) = ( A S ( T ` B ) ) ) $=
      ( cnv wcel wa co cfv wceq eqid w3a cc cn0v cpv simpl simprl simprr simpl1
      nvzcl syl lnolin syl13anc nvscl syl3anc nv0rid syl2anc fveq2d lno0 oveq2d
      cba adantr simpl2 wf lnof ffvelcdmd eqtrd 3eqtr3d ) FNOZHNOZEGOZUAZAUBOZB
      IOZPZPZABCQZFUCRZFUDRZQZERZABERZDQZVQERZHUDRZQZVPERWBVOVKVLVMVQIOZVTWESVK
      VNUEVKVLVMUFZVKVLVMUGZVOVHWFVHVIVJVNUHZFIVQJVQTZUIUJABVQCDEFVRWDGHIHUTRZJ
      WKTZVRTZWDTZKLMUKULVOVSVPEVOVHVPIOZVSVPSWIVOVHVLVMWOWIWGWHABCFIJKUMUNVPFV
      RIVQJWMWJUOUPUQVOWEWBHUCRZWDQZWBVKWEWQSVNVKWCWPWBWDVQEFGHIWKWPJWLWJWPTZMU
      RUSVAVOVIWBWKOZWQWBSVHVIVJVNVBZVOVIVLWAWKOWSWTWGVOIWKBEVKIWKEVCVNEFGHIWKJ
      WLMVDVAWHVEAWADHWKWLLUMUNWBHWDWKWPWLWNWRUOUPVFVG $.
  $}

  ${
    nvo00.1 $e |- X = ( BaseSet ` U ) $.
    $( Two ways to express a zero operator.  (Contributed by NM, 27-Nov-2007.)
       (New usage is discouraged.) $)
    nvo00 $p |- ( ( U e. NrmCVec /\ T : X --> Y ) ->
                  ( T = ( X X. { Z } ) <-> ran T = { Z } ) ) $=
      ( wf wfn c0 wne csn cxp wceq crn wb cnv wcel ffn cn0v cfv eqid nvzcl ne0d
      fconst5 syl2anr ) CDAGACHCIJACEKZLMANUFMOBPQZCDARUGCBSTZBCUHFUHUAUBUCCEAU
      DUE $.
  $}

  ${
    $d t u w x z U $.  $d t u w x z W $.  $d t u w z X $.  $d t u w x Y $.
    $d t u w L $.  $d t u w M $.  $d t x z T $.
    nmoofval.1 $e |- X = ( BaseSet ` U ) $.
    nmoofval.2 $e |- Y = ( BaseSet ` W ) $.
    nmoofval.3 $e |- L = ( normCV ` U ) $.
    nmoofval.4 $e |- M = ( normCV ` W ) $.
    nmoofval.6 $e |- N = ( U normOpOLD W ) $.
    $( The operator norm function.  (Contributed by NM, 6-Nov-2007.)  (Revised
       by Mario Carneiro, 16-Nov-2013.)  (New usage is discouraged.) $)
    nmoofval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> N =
       ( t e. ( Y ^m X ) |-> sup ( { x | E. z e. X
         ( ( L ` z ) <_ 1 /\ x = ( M ` ( t ` z ) ) ) } , RR* , < ) ) ) $=
      ( cmap cv cfv cba cnmcv vu vw cnv wcel wa cnmoo cle wbr wceq wrex cab cxr
      co c1 clt csup fveq2 eqtr4di oveq2d fveq1d breq1d anbi1d rexeqbidv abbidv
      supeq1d mpteq12dv oveq1d eqeq2d anbi2d rexbidv df-nmoo mptex ovmpo eqtrid
      cmpt ovex ) DUCUDHUCUDUEGDHUFUMCJIPUMZBQZERZUNUGUHZAQZVRCQRZFRZUIZUEZBIUJ
      ZAUKZULUOUPZVOZOUAUBDHUCUCCUBQZSRZUAQZSRZPUMZVRWLTRZRZUNUGUHZWAWBWJTRZRZU
      IZUEZBWMUJZAUKZULUOUPZVOWIUFCWKIPUMZVTWTUEZBIUJZAUKZULUOUPZVOWLDUIZCWNXDX
      EXIXJWMIWKPXJWMDSRIWLDSUQKURZUSXJULXCXHUOXJXBXGAXJXAXFBWMIXKXJWQVTWTXJWPV
      SUNUGXJVRWOEXJWODTREWLDTUQMURUTVAVBVCVDVEVFWJHUIZCXEXIVQWHXLWKJIPXLWKHSRJ
      WJHSUQLURVGXLULXHWGUOXLXGWFAXLXFWEBIXLWTWDVTXLWSWCWAXLWBWRFXLWRHTRFWJHTUQ
      NURUTVHVIVJVDVEVFABUBUACVKCVQWHJIPVPVLVMVN $.

    $( The operator norm function.  (Contributed by NM, 27-Nov-2007.)  (Revised
       by Mario Carneiro, 16-Nov-2013.)  (New usage is discouraged.) $)
    nmooval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
      ( N ` T ) = sup ( { x | E. z e. X
        ( ( L ` z ) <_ 1 /\ x = ( M ` ( T ` z ) ) ) } , RR* , < ) ) $=
      ( vt cfv wceq cxr clt cnv wcel wf cv c1 cle wbr wa wrex cab csup cmap cba
      co fvexi elmap nmoofval fveq1d fveq1 fveq2d eqeq2d anbi2d rexbidv supeq1d
      cmpt abbidv eqid xrltso supex fvmpt sylan9eq sylan2br 3impa ) DUAUBZHUAUB
      ZIJCUCZCGQZBUDZEQUEUFUGZAUDZVRCQZFQZRZUHZBIUIZAUJZSTUKZRZVPVNVOUHZCJIULUN
      ZUBZWHJICJHUMLUOIDUMKUOUPWIWKVQCPWJVSVTVRPUDZQZFQZRZUHZBIUIZAUJZSTUKZVEZQ
      WGWICGWTABPDEFGHIJKLMNOUQURPCWSWGWJWTWLCRZSWRWFTXAWQWEAXAWPWDBIXAWOWCVSXA
      WNWBVTXAWMWAFVRWLCUSUTVAVBVCVFVDWTVGSWFTVHVIVJVKVLVM $.
  $}

  ${
    $d x z T $.  $d x z W $.  $d x z X $.  $d x z Y $.
    nmosetre.2 $e |- Y = ( BaseSet ` W ) $.
    nmosetre.4 $e |- N = ( normCV ` W ) $.
    $( The set in the supremum of the operator norm definition ~ df-nmoo is a
       set of reals.  (Contributed by NM, 13-Nov-2007.)
       (New usage is discouraged.) $)
    nmosetre $p |- ( ( W e. NrmCVec /\ T : X --> Y ) -> {
     x | E. z e. X ( ( M ` z ) <_ 1 /\ x = ( N ` ( T ` z ) ) ) } C_ RR ) $=
      ( cnv wcel wf wa cv cfv c1 cle wbr cr wceq wrex nvcl sylan2 anassrs eleq1
      ffvelcdm imbitrrid impcom adantrl rexlimdva2 abssdv ) FKLZGHCMZNZBOZDPQRS
      ZAOZUPCPZEPZUAZNZBGUBATUOVBURTLZBGUOUPGLZNZVAVCUQVAVEVCVEVCVAUTTLZUMUNVDV
      FUNVDNUMUSHLVFGHUPCUGUSFEHIJUCUDUEURUTTUFUHUIUJUKUL $.
  $}

  ${
    $d x y M $.  $d x y N $.  $d x y T $.  $d x y X $.  $d x y Z $.
    nmosetn0.1 $e |- X = ( BaseSet ` U ) $.
    nmosetn0.5 $e |- Z = ( 0vec ` U ) $.
    nmosetn0.4 $e |- M = ( normCV ` U ) $.
    $( The set in the supremum of the operator norm definition ~ df-nmoo is
       nonempty.  (Contributed by NM, 8-Dec-2007.)
       (New usage is discouraged.) $)
    nmosetn0 $p |- ( U e. NrmCVec -> ( N ` ( T ` Z ) ) e. { x | E. y e. X (
       ( M ` y ) <_ 1 /\ x = ( N ` ( T ` y ) ) ) } ) $=
      ( wcel cv cfv c1 cle wbr wceq wa wrex cnv cab cc0 nvz0 0le1 eqbrtrdi eqid
      nvzcl jctir fveq2 breq1d 2fveq3 eqeq2d anbi12d rspcev syl2anc fvex anbi2d
      eqeq1 rexbidv elab sylibr ) DUALZBMZENZOPQZHCNZFNZVDCNFNZRZSZBGTZVHVFAMZV
      IRZSZBGTZAUBLVCHGLHENZOPQZVHVHRZSZVLDGHIJUHVCVRVSVCVQUCOPDEHJKUDUEUFVHUGU
      IVKVTBHGVDHRZVFVRVJVSWAVEVQOPVDHEUJUKWAVIVHVHVDHFCULUMUNUOUPVPVLAVHVGFUQV
      MVHRZVOVKBGWBVNVJVFVMVHVIUSURUTVAVB $.
  $}

  ${
    $d x z T $.  $d x z U $.  $d x z W $.  $d x z X $.  $d x z Y $.
    nmoxr.1 $e |- X = ( BaseSet ` U ) $.
    nmoxr.2 $e |- Y = ( BaseSet ` W ) $.
    nmoxr.3 $e |- N = ( U normOpOLD W ) $.
    $( The norm of an operator is an extended real.  (Contributed by NM,
       27-Nov-2007.)  (New usage is discouraged.) $)
    nmoxr $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
              ( N ` T ) e. RR* ) $=
      ( vz vx cnv wcel wf cfv cv cnmcv wa cxr eqid w3a c1 cle wbr wceq wrex cab
      clt csup nmooval wss nmosetre ressxr sstrdi supxrcl syl 3adant1 eqeltrd
      cr ) BLMZDLMZEFANZUAACOJPZBQOZOUBUCUDKPVCAODQOZOUERJEUFKUGZSUHUIZSKJABVDV
      ECDEFGHVDTVETZIUJVAVBVGSMZUTVAVBRZVFSUKVIVJVFUSSKJAVDVEDEFHVHULUMUNVFUOUP
      UQUR $.

    $( The norm of an operator is nonnegative.  (Contributed by NM,
       8-Dec-2007.)  (New usage is discouraged.) $)
    nmooge0 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
                  0 <_ ( N ` T ) ) $=
      ( vz vx cnv wcel cc0 cfv cnmcv cxr eqid cle wbr wf w3a cn0v 0xr a1i simp2
      cr nvzcl ffvelcdm sylan2 ancoms 3adant2 nvcl syl2anc rexrd nmoxr nvge0 cv
      wceq wrex cab clt csup wss nmosetre ressxr sstrdi nmosetn0 supxrub syl2an
      c1 wa 3impa 3comr nmooval breqtrrd xrletrd ) BLMZDLMZEFAUAZUBZNBUCOZAOZDP
      OZOZACOZNQMWAUDUEWAWEWAVSWCFMZWEUGMVRVSVTUFZVRVTWGVSVTVRWGVRVTWBEMWGBEWBG
      WBRZUHEFWBAUIUJUKULZWCDWDFHWDRZUMUNUOABCDEFGHIUPWAVSWGNWESTWHWJWCDWDFHWKU
      QUNWAWEJURZBPOZOVKSTKURWLAOWDOUSVLJEUTKVAZQVBVCZWFSVSVTVRWEWOSTZVSVTVRWPV
      SVTVLZWNQVDWEWNMWPVRWQWNUGQKJAWMWDDEFHWKVEVFVGKJABWMWDEWBGWIWMRZVHWNWEVIV
      JVMVNKJABWMWDCDEFGHWRWKIVOVPVQ $.

    $( The norm of an operator is either real or plus infinity.  (Contributed
       by NM, 8-Dec-2007.)  (New usage is discouraged.) $)
    nmorepnf $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
                   ( ( N ` T ) e. RR <-> ( N ` T ) =/= +oo ) ) $=
      ( vz vx cnv wcel cv cnmcv cfv cr cpnf wne eqid wf w3a c1 cle wceq wa wrex
      wbr cab cxr clt csup wb wss c0 nmosetre cn0v nmosetn0 ne0d supxrre2 3impb
      syl2anr nmooval eleq1d neeq1d 3bitr4d ) BLMZDLMZEFAUAZUBZJNZBOPZPUCUDUHKN
      VKAPDOPZPUEUFJEUGKUIZUJUKULZQMZVORSZACPZQMVRRSVGVHVIVPVQUMZVHVIUFVNQUNVNU
      OSVSVGKJAVLVMDEFHVMTZUPVGVNBUQPZAPVMPKJABVLVMEWAGWATVLTZURUSVNUTVBVAVJVRV
      OQKJABVLVMCDEFGHWBVTIVCZVDVJVRVORWCVEVF $.

    $( The norm of any operator is real iff it is less than plus infinity.
       (Contributed by NM, 8-Dec-2007.)  (New usage is discouraged.) $)
    nmoreltpnf $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
                   ( ( N ` T ) e. RR <-> ( N ` T ) < +oo ) ) $=
      ( cnv wcel wf w3a cfv cr cpnf wne clt wbr nmorepnf cxr wceq wn wb nltpnft
      nmoxr syl necon2abid bitr4d ) BJKDJKEFALMZACNZOKUKPQUKPRSZABCDEFGHITUJULU
      KPUJUKUAKUKPUBULUCUDABCDEFGHIUFUKUEUGUHUI $.

    $( The norm of an operator is greater than minus infinity.  (Contributed by
       NM, 8-Dec-2007.)  (New usage is discouraged.) $)
    nmogtmnf $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) ->
                  -oo < ( N ` T ) ) $=
      ( cnv wcel wf w3a cfv cr cpnf wceq wn wb wo cmnf clt wbr wne df-ne bitrdi
      nmorepnf xor3 nbior sylbir mnfltxr 3syl ) BJKDJKEFALMZACNZOKZUNPQZRZSZUOU
      PTZUAUNUBUCUMUOUNPUDUQABCDEFGHIUGUNPUEUFURUOUPSRUSUOUPUHUOUPUIUJUNUKUL $.
  $}

  ${
    $d x y A $.  $d x y L $.  $d x y M $.  $d x y T $.  $d x y U $.
    $d x y W $.  $d x y X $.  $d x y Y $.
    nmoolb.1 $e |- X = ( BaseSet ` U ) $.
    nmoolb.2 $e |- Y = ( BaseSet ` W ) $.
    nmoolb.l $e |- L = ( normCV ` U ) $.
    nmoolb.m $e |- M = ( normCV ` W ) $.
    nmoolb.3 $e |- N = ( U normOpOLD W ) $.
    $( A lower bound for an operator norm.  (Contributed by NM, 8-Dec-2007.)
       (New usage is discouraged.) $)
    nmoolb $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) /\
         ( A e. X /\ ( L ` A ) <_ 1 ) ) -> ( M ` ( T ` A ) ) <_ ( N ` T ) ) $=
      ( vy vx cfv cle wa wceq cnv wcel wf w3a c1 wbr cv wrex cab cxr clt wss cr
      nmosetre ressxr sstrdi 3adant1 fveq2 breq1d 2fveq3 eqeq2d anbi12d biantru
      csup eqid bitr4di rspcev fvex eqeq1 anbi2d rexbidv sylibr supxrub nmooval
      elab syl2an adantr breqtrrd ) CUAUBZGUAUBZHIBUCZUDZAHUBADQZUERUFZSZSABQZE
      QZOUGZDQZUERUFZPUGZWHBQEQZTZSZOHUHZPUIZUJUKVDZBFQZRWBWPUJULZWGWPUBZWGWQRU
      FWEVTWAWSVSVTWASWPUMUJPOBDEGHIKMUNUOUPUQWEWJWGWLTZSZOHUHZWTXBWDOAHWHATZXB
      WDWGWGTZSWDXDWJWDXAXEXDWIWCUERWHADURUSXDWLWGWGWHAEBUTVAVBXEWDWGVEVCVFVGWO
      XCPWGWFEVHWKWGTZWNXBOHXFWMXAWJWKWGWLVIVJVKVOVLWPWGVMVPWBWRWQTWEPOBCDEFGHI
      JKLMNVNVQVR $.
  $}

  ${
    $d x z A $.  $d f k r x y z L $.  $d x y U $.  $d x y W $.  $d k r x y Y $.
    $d f k r x y z M $.  $d f k r x y z T $.  $d f k r x y z X $.
    $d k r y N $.
    nmoubi.1 $e |- X = ( BaseSet ` U ) $.
    nmoubi.y $e |- Y = ( BaseSet ` W ) $.
    nmoubi.l $e |- L = ( normCV ` U ) $.
    nmoubi.m $e |- M = ( normCV ` W ) $.
    nmoubi.3 $e |- N = ( U normOpOLD W ) $.
    nmoubi.u $e |- U e. NrmCVec $.
    nmoubi.w $e |- W e. NrmCVec $.
    $( An upper bound for an operator norm.  (Contributed by NM, 11-Dec-2007.)
       (New usage is discouraged.) $)
    nmoubi $p |- ( ( T : X --> Y /\ A e. RR* ) -> ( ( N ` T ) <_ A <->
      A. x e. X ( ( L ` x ) <_ 1 -> ( M ` ( T ` x ) ) <_ A ) ) ) $=
      ( vz cle wi vy wf cxr wcel wa cfv wbr cv c1 wceq wrex cab wral clt wb cnv
      csup nmooval mp3an12 breq1d adantr wss cr nmosetre ressxr supxrleub sylan
      mpan sstrdi bitrd eqeq1 anbi2d rexbidv ralab ralcom4 ancomst impexp bitri
      wal albii fvex breq1 imbi2d ceqsalv ralbii r19.23v 3bitr3i bitr4i bitrdi
      ) IJCUBZBUCUDZUEZCGUFZBSUGZRUHZBSUGZRAUHZEUFUISUGZUAUHZWQCUFZFUFZUJZUEZAI
      UKZUAULZUMZWRXABSUGZTZAIUMZWLWNXEUCUNUQZBSUGZXFWJWNXKUOWKWJWMXJBSDUPUDHUP
      UDZWJWMXJUJPQUAACDEFGHIJKLMNOURUSUTVAWJXEUCVBWKXKXFUOWJXEVCUCXLWJXEVCVBQU
      AACEFHIJLNVDVHVEVIRXEBVFVGVJXFWRWOXAUJZUEZAIUKZWPTZRVSZXIXDXOWPRUAWSWOUJZ
      XCXNAIXRXBXMWRWSWOXAVKVLVMVNXNWPTZRVSZAIUMXSAIUMZRVSXIXQXSARIVOXTXHAIXTXM
      WRWPTZTZRVSXHXSYCRXSXMWRUEWPTYCWRXMWPVPXMWRWPVQVRVTYBXHRXAWTFWAXMWPXGWRWO
      XABSWBWCWDVRWEYAXPRXNWPAIWFVTWGWHWI $.

    $( An upper bound for an operator norm.  (Contributed by NM, 12-Dec-2007.)
       (New usage is discouraged.) $)
    nmoub3i $p |- ( ( T : X --> Y /\ A e. RR /\ A. x e. X
  ( M ` ( T ` x ) ) <_ ( A x. ( L ` x ) ) ) -> ( N ` T ) <_ ( abs ` A ) ) $=
      ( wcel cle wbr wf cr cv cfv cmul co wral cabs wa c1 cnv nvcl mpan remulcl
      wi sylan2 adantr recn abscld syl2an ad2antrr cc0 simpl nvge0 adantl leabs
      jca lemul1a syl31anc 1red absge0d 3jca lemul2a sylan wceq mulridd breqtrd
      w3a recnd adantlll ffvelcdm sylancr adantlr adantll ad2antlr letr syl3anc
      letrd mpan2d ex com23 ralimdva imp cxr rexrd nmoubi biimpar syldan 3impa
      wb ) IJCUAZBUBRZAUCZCUDZFUDZBXCEUDZUEUFZSTZAIUGZCGUDBUHUDZSTZXAXBUIZXIXFU
      JSTZXEXJSTZUOZAIUGZXKXLXIXPXLXHXOAIXLXCIRZUIZXMXHXNXRXMXHXNUOXRXMUIXHXGXJ
      STZXNXBXQXMXSXAXBXQUIZXMUIZXGXJXFUEUFZXJXTXGUBRZXMXQXBXFUBRZYCDUKRZXQYDPX
      CDEIKMULUMZBXFUNUPZUQXTYBUBRZXMXBXJUBRZYDYHXQXBBBURZUSZYFXJXFUNUTUQXBYIXQ
      XMYKVAXTXGYBSTZXMXTXBYIYDVBXFSTZUIZBXJSTZYLXBXQVCXBYIXQYKUQZXQYNXBXQYDYMY
      FYEXQYMPXCDEIKMVDUMVGVEXBYOXQBVFUQBXJXFVHVIUQYAYBXJUJUEUFZXJSXTYDUJUBRZYI
      VBXJSTZUIZVRXMYBYQSTXTYDYRYTXQYDXBYFVEXTVJXTYIYSYPXBYSXQXBBYJVKUQVGVLXFUJ
      XJVMVNXBYQXJVOXQXMXBXJXBXJYKVSVPVAVQWHVTXRXHXSUIXNUOZXMXRXEUBRZYCYIUUAXAX
      QUUBXBXAXQUIHUKRXDJRUUBQIJXCCWAXDHFJLNULWBWCXBXQYCXAYGWDXBYIXAXQYKWEXEXGX
      JWFWGUQWIWJWKWLWMXLXKXPXBXAXJWNRXKXPWTXBXJYKWOAXJCDEFGHIJKLMNOPQWPUPWQWRW
      S $.

    $( An upper bound for an operator norm.  (Contributed by NM, 11-Dec-2007.)
       (New usage is discouraged.) $)
    nmoub2i $p |- ( ( T : X --> Y /\ ( A e. RR /\ 0 <_ A ) /\ A. x e. X
  ( M ` ( T ` x ) ) <_ ( A x. ( L ` x ) ) ) -> ( N ` T ) <_ A ) $=
      ( cle wbr cfv wf cr wcel cc0 wa cv cmul co wral w3a cabs nmoub3i 3adant2r
      wceq absid 3ad2ant2 breqtrd ) IJCUAZBUBUCZUDBRSZUEZAUFZCTFTBVBETUGUHRSAIU
      IZUJCGTZBUKTZBRURUSVCVDVERSUTABCDEFGHIJKLMNOPQULUMVAURVEBUNVCBUOUPUQ $.

    $( Two ways to express that an operator is bounded.  (Contributed by NM,
       11-Jan-2008.)  (New usage is discouraged.) $)
    nmobndi $p |- ( T : X --> Y -> ( ( N ` T ) e. RR <->
     E. r e. RR A. y e. X ( ( L ` y ) <_ 1 -> ( M ` ( T ` y ) ) <_ r ) ) ) $=
      ( cr wcel cle wf cfv cv wbr wrex c1 wral leid breq2 rspcev mpdan cxr cmnf
      wi wa clt cnv nmoxr mp3an12 adantr simprl nmogtmnf simprr xrre rexlimdvaa
      syl22anc impbid2 wb rexr nmoubi sylan2 rexbidva bitrd ) HIBUAZBFUBZRSZVOJ
      UCZTUDZJRUEZAUCZDUBUFTUDVTBUBEUBVQTUDUNAHUGZJRUEVNVPVSVPVOVOTUDZVSVOUHVRW
      BJVORVQVOVOTUIUJUKVNVRVPJRVNVQRSZVRUOZUOVOULSZWCUMVOUPUDZVRVPVNWEWDCUQSZG
      UQSZVNWEPQBCFGHIKLOURUSUTVNWCVRVAVNWFWDWGWHVNWFPQBCFGHIKLOVBUSUTVNWCVRVCV
      OVQVDVFVEVGVNVRWAJRWCVNVQULSVRWAVHVQVIAVQBCDEFGHIKLMNOPQVJVKVLVM $.

    $( Two ways two express that an operator is unbounded.  (Contributed by NM,
       11-Jan-2008.)  (New usage is discouraged.) $)
    nmounbi $p |- ( T : X --> Y -> ( ( N ` T ) = +oo <->
      A. r e. RR E. y e. X ( ( L ` y ) <_ 1 /\ r < ( M ` ( T ` y ) ) ) ) ) $=
      ( cfv cr wcel wf cv c1 cle wbr clt wa wrex wral cpnf wi wne wn nmobndi wb
      cnv nmorepnf mp3an12 ffvelcdm nvcl sylancr lenlt sylan an32s imbi2d imnan
      bitrdi ralbidva ralnex rexbidva rexnal 3bitr3d necon4abid ) HIBUAZAUBZDRU
      CUDUEZJUBZVOBRZERZUFUEZUGZAHUHZJSUIZBFRZUJVNWDSTZVPVSVQUDUEZUKZAHUIZJSUHZ
      WDUJULZWCUMZABCDEFGHIJKLMNOPQUNCUPTGUPTZVNWEWJUOPQBCFGHIKLOUQURVNWIWBUMZJ
      SUHWKVNWHWMJSVNVQSTZUGZWHWAUMZAHUIWMWOWGWPAHWOVOHTZUGZWGVPVTUMZUKWPWRWFWS
      VPVNWQWNWFWSUOZVNWQUGZVSSTZWNWTXAWLVRITXBQHIVOBUSVRGEILNUTVAVSVQVBVCVDVEV
      PVTVFVGVHWAAHVIVGVJWBJSVKVGVLVM $.

    $( An unbounded operator determines an unbounded sequence.  (Contributed by
       NM, 11-Jan-2008.)  (Revised by Mario Carneiro, 7-Apr-2013.)
       (New usage is discouraged.) $)
    nmounbseqi $p |- ( ( T : X --> Y /\ ( N ` T ) = +oo ) ->
         E. f ( f : NN --> X /\ A. k e. NN ( ( L ` ( f ` k ) ) <_ 1 /\
          k < ( M ` ( T ` ( f ` k ) ) ) ) ) ) $=
      ( vy cfv cn wf cpnf wceq wa cv c1 cle wbr clt wrex cr wral nmounbi biimpa
      wex wcel nnre imim1i ralimi2 cba fvexi nnenom fveq2 breq1d 2fveq3 anbi12d
      breq2d axcc4 3syl ) IJAUAZAGSUBUCZUDRUEZESZUFUGUHZDUEZVLASFSZUIUHZUDZRIUJ
      ZDUKULZVSDTULTICUEZUAVOWASZESZUFUGUHZVOWBASFSZUIUHZUDZDTULUDCUOVJVKVTRABE
      FGHIJDKLMNOPQUMUNVSVSDUKTVOTUPVOUKUPVSVOUQURUSVRWGRICDTIBUTKVAVBVLWBUCZVN
      WDVQWFWHVMWCUFUGVLWBEVCVDWHVPWEVOUIVLWBFAVEVGVFVHVI $.

    $( Alternate shorter proof of ~ nmounbseqi based on Axioms ~ ax-reg and
       ~ ax-ac2 instead of ~ ax-cc .  (Contributed by NM, 11-Jan-2008.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    nmounbseqiALT $p |- ( ( T : X --> Y /\ ( N ` T ) = +oo ) ->
         E. f ( f : NN --> X /\ A. k e. NN ( ( L ` ( f ` k ) ) <_ 1 /\
          k < ( M ` ( T ` ( f ` k ) ) ) ) ) ) $=
      ( vy cfv cn wf cpnf wceq wa cv c1 cle wbr clt wrex cr wral nmounbi biimpa
      wex wcel nnre imim1i ralimi2 nnex fveq2 breq1d fveq2d breq2d anbi12d ac6s
      3syl ) IJAUAZAGSUBUCZUDRUEZESZUFUGUHZDUEZVJASZFSZUIUHZUDZRIUJZDUKULZVRDTU
      LTICUEZUAVMVTSZESZUFUGUHZVMWAASZFSZUIUHZUDZDTULUDCUOVHVIVSRABEFGHIJDKLMNO
      PQUMUNVRVRDUKTVMTUPVMUKUPVRVMUQURUSVQWGDRTICUTVJWAUCZVLWCVPWFWHVKWBUFUGVJ
      WAEVAVBWHVOWEVMUIWHVNWDFVJWAAVAVCVDVEVFVG $.

    $( A bounded sequence determines a bounded operator.  (Contributed by NM,
       18-Jan-2008.)  (Revised by Mario Carneiro, 7-Apr-2013.)
       (New usage is discouraged.) $)
    nmobndseqi $p |- ( ( T : X --> Y /\
         A. f ( ( f : NN --> X /\ A. k e. NN ( L ` ( f ` k ) ) <_ 1 ) ->
        E. k e. NN ( M ` ( T ` ( f ` k ) ) ) <_ k ) ) -> ( N ` T ) e. RR ) $=
      ( cn cfv wi vy wf cv c1 cle wbr wral wa wrex cr wcel impexp r19.35 imbi2i
      wal bitr4i albii wn wex cba fvexi nnenom wceq fveq2 breq1d 2fveq3 imbi12d
      notbid axcc4 con3i dfrex2 alinexa bitri dfral2 rexbii rexnal 3imtr4i nnre
      anim1i reximi2 syl sylbi nmobndi imbitrrid imp ) IJAUBZRICUCZUBZDUCZWGSZE
      SZUDUEUFZDRUGZUHWJASFSZWIUEUFZDRUIZTZCUOZAGSUJUKZWRWSWFUAUCZESZUDUEUFZWTA
      SFSZWIUEUFZTZUAIUGZDUJUIZWRWHWLWOTZDRUIZTZCUOZXGWQXJCWQWHWMWPTZTXJWHWMWPU
      LXIXLWHWLWODRUMUNUPUQXKXFDRUIZXGWHXHURZDRUGZUHCUSZURZXEURZUAIUIZDRUGZURZX
      KXMXTXPXRXNUAICDRIBUTKVAVBWTWJVCZXEXHYBXBWLXDWOYBXAWKUDUEWTWJEVDVEYBXCWNW
      IUEWTWJFAVFVEVGVHVIVJXKWHXOURZTZCUOXQXJYDCXIYCWHXHDRVKUNUQWHXOCVLVMXMXSUR
      ZDRUIYAXFYEDRXEUAIVNVOXSDRVPVMVQXFXFDRUJWIRUKWIUJUKXFWIVRVSVTWAWBUAABEFGH
      IJDKLMNOPQWCWDWE $.

    $( Alternate shorter proof of ~ nmobndseqi based on Axioms ~ ax-reg and
       ~ ax-ac2 instead of ~ ax-cc .  (Contributed by NM, 18-Jan-2008.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    nmobndseqiALT $p |- ( ( T : X --> Y /\
         A. f ( ( f : NN --> X /\ A. k e. NN ( L ` ( f ` k ) ) <_ 1 ) ->
        E. k e. NN ( M ` ( T ` ( f ` k ) ) ) <_ k ) ) -> ( N ` T ) e. RR ) $=
      ( cn cfv cle vy wf cv c1 wbr wral wa wrex wi cr wcel impexp r19.35 imbi2i
      wal bitr4i albii nnex wceq breq1d fveq2d imbi12d ac6n nnre anim1i reximi2
      fveq2 syl sylbi nmobndi imbitrrid imp ) IJAUBZRICUCZUBZDUCZVNSZESZUDTUEZD
      RUFZUGVQASZFSZVPTUEZDRUHZUIZCUOZAGSUJUKZWFWGVMUAUCZESZUDTUEZWHASZFSZVPTUE
      ZUIZUAIUFZDUJUHZWFVOVSWCUIZDRUHZUIZCUOZWPWEWSCWEVOVTWDUIZUIWSVOVTWDULWRXA
      VOVSWCDRUMUNUPUQWTWODRUHWPWNWQDUARICURWHVQUSZWJVSWMWCXBWIVRUDTWHVQEVGUTXB
      WLWBVPTXBWKWAFWHVQAVGVAUTVBVCWOWODRUJVPRUKVPUJUKWOVPVDVEVFVHVIUAABEFGHIJD
      KLMNOPQVJVKVL $.
  $}

  ${
    $d t u w L $.  $d t u w N $.  $d t T $.  $d t u w U $.  $d t u w W $.
    bloval.3 $e |- N = ( U normOpOLD W ) $.
    bloval.4 $e |- L = ( U LnOp W ) $.
    bloval.5 $e |- B = ( U BLnOp W ) $.
    $( The class of bounded linear operators between two normed complex vector
       spaces.  (Contributed by NM, 6-Nov-2007.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    bloval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) ->
                   B = { t e. L | ( N ` t ) < +oo } ) $=
      ( vu vw cnv co cv cfv cpnf clt wbr cnmoo clno wcel cblo crab oveq1 fveq1d
      wa wceq breq1d rabeqbidv oveq2 eqtr4di df-blo ovexi rabex ovmpo eqtrid )
      CLUAFLUAUFBCFUBMANZEOZPQRZADUCZIJKCFLLUQJNZKNZSMZOZPQRZAVAVBTMZUCUTUBUQCV
      BSMZOZPQRZACVBTMZUCVACUGZVEVIAVFVJVACVBTUDVKVDVHPQVKUQVCVGVACVBSUDUEUHUIV
      BFUGZVIUSAVJDVLVJCFTMDVBFCTUJHUKVLVHURPQVLUQVGEVLVGCFSMEVBFCSUJGUKUEUHUIK
      JAULUSADDCFTHUMUNUOUP $.

    $( The predicate "is a bounded linear operator."  (Contributed by NM,
       6-Nov-2007.)  (New usage is discouraged.) $)
    isblo $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> ( T e. B <->
      ( T e. L /\ ( N ` T ) < +oo ) ) ) $=
      ( vt cnv wcel wa cv cfv cpnf clt wbr crab bloval eleq2d wceq fveq2 breq1d
      elrab bitrdi ) CKLFKLMZBALBJNZEOZPQRZJDSZLBDLBEOZPQRZMUGAUKBJACDEFGHITUAU
      JUMJBDUHBUBUIULPQUHBEUCUDUEUF $.

    $( The predicate "is a bounded linear operator."  (Contributed by NM,
       8-Dec-2007.)  (New usage is discouraged.) $)
    isblo2 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> ( T e. B <->
      ( T e. L /\ ( N ` T ) e. RR ) ) ) $=
      ( cnv wcel wa cfv cpnf clt wbr cr isblo cba eqid lnof nmoreltpnf syld3an3
      wb wf 3expa pm5.32da bitr4d ) CJKZFJKZLZBAKBDKZBEMZNOPZLULUMQKZLABCDEFGHI
      RUKULUOUNUIUJULUOUNUDZUIUJULCSMZFSMZBUEUPBCDFUQURUQTZURTZHUABCEFUQURUSUTG
      UBUCUFUGUH $.
  $}

  ${
    bloln.4 $e |- L = ( U LnOp W ) $.
    bloln.5 $e |- B = ( U BLnOp W ) $.
    $( A bounded operator is a linear operator.  (Contributed by NM,
       8-Dec-2007.)  (New usage is discouraged.) $)
    bloln $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. B ) -> T e. L ) $=
      ( cnv wcel wa cnmoo co cfv cpnf clt wbr eqid isblo simprbda 3impa ) CHIZE
      HIZBAIZBDIZUAUBJUCUDBCEKLZMNOPABCDUEEUEQFGRST $.
  $}

  ${
    blof.1 $e |- X = ( BaseSet ` U ) $.
    blof.2 $e |- Y = ( BaseSet ` W ) $.
    blof.5 $e |- B = ( U BLnOp W ) $.
    $( A bounded operator is an operator.  (Contributed by NM, 8-Dec-2007.)
       (New usage is discouraged.) $)
    blof $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. B ) -> T : X --> Y ) $=
      ( cnv wcel clno co wf eqid bloln lnof syld3an3 ) CJKDJKBAKBCDLMZKEFBNABCS
      DSOZIPBCSDEFGHTQR $.
  $}

  ${
    nmblore.1 $e |- X = ( BaseSet ` U ) $.
    nmblore.2 $e |- Y = ( BaseSet ` W ) $.
    nmblore.3 $e |- N = ( U normOpOLD W ) $.
    nmblore.5 $e |- B = ( U BLnOp W ) $.
    $( The norm of a bounded operator is a real number.  (Contributed by NM,
       8-Dec-2007.)  (New usage is discouraged.) $)
    nmblore $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. B ) ->
                ( N ` T ) e. RR ) $=
      ( cnv wcel w3a cfv cr clt wbr syld3an3 wa cmnf cpnf wf blof nmogtmnf clno
      co eqid isblo simplbda 3impa cxr wb nmoxr xrrebnd syl mpbir2and ) CLMZELM
      ZBAMZNZBDOZPMZUAVBQRZVBUBQRZURUSUTFGBUCZVDABCEFGHIKUDZBCDEFGHIJUESURUSUTV
      EURUSTUTBCEUFUGZMVEABCVHDEJVHUHKUIUJUKVAVBULMZVCVDVETUMURUSUTVFVIVGBCDEFG
      HIJUNSVBUOUPUQ $.
  $}

  ${
    $d u w U $.  $d u w W $.  $d u w X $.  $d u w Z $.
    0oval.1 $e |- X = ( BaseSet ` U ) $.
    0oval.6 $e |- Z = ( 0vec ` W ) $.
    0oval.0 $e |- O = ( U 0op W ) $.
    $( The zero operator between two normed complex vector spaces.
       (Contributed by NM, 28-Nov-2007.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    0ofval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> O = ( X X. { Z } ) ) $=
      ( vu vw cnv wcel c0o csn cxp cv cba cfv cn0v wceq wa fveq2 eqtr4di xpeq1d
      co sneqd xpeq2d df-0o fvexi snex xpex ovmpo eqtrid ) AKLCKLUABACMUEDENZOZ
      HIJACKKIPZQRZJPZSRZNZOUOMDUTOUPATZUQDUTVAUQAQRDUPAQUBFUCUDURCTZUTUNDVBUSE
      VBUSCSREURCSUBGUCUFUGJIUHDUNDAQFUIEUJUKULUM $.

    $( Value of the zero operator.  (Contributed by NM, 28-Nov-2007.)
       (New usage is discouraged.) $)
    0oval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ A e. X ) ->
            ( O ` A ) = Z ) $=
      ( cnv wcel w3a cfv csn cxp wceq wa 0ofval fveq1d 3adant3 cn0v fvexi eqtrd
      fvconst2 3ad2ant3 ) BJKZDJKZAEKZLACMZAEFNOZMZFUFUGUIUKPUHUFUGQACUJBCDEFGH
      IRSTUHUFUKFPUGEFAFDUAHUBUDUEUC $.
  $}

  ${
    0oo.1 $e |- X = ( BaseSet ` U ) $.
    0oo.2 $e |- Y = ( BaseSet ` W ) $.
    0oo.0 $e |- Z = ( U 0op W ) $.
    $( The zero operator is an operator.  (Contributed by NM, 28-Nov-2007.)
       (New usage is discouraged.) $)
    0oo $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> Z : X --> Y ) $=
      ( cnv wcel wa wf cn0v cfv csn cxp wss fvex fconst eqid nvzcl snssd adantl
      fss sylancr 0ofval feq1d mpbird ) AIJZBIJZKZCDELCDCBMNZOZPZLZUJUOUIUJCUMU
      NLUMDQUOCULBMRSUJULDBDULGULTZUAUBCUMDUNUDUEUCUKCDEUNAEBCULFUPHUFUGUH $.
  $}

  ${
    $d x y z U $.  $d x y z W $.  $d x y z Z $.
    0lno.0 $e |- Z = ( U 0op W ) $.
    0lno.7 $e |- L = ( U LnOp W ) $.
    $( The zero operator is linear.  (Contributed by NM, 28-Nov-2007.)
       (Revised by Mario Carneiro, 19-Nov-2013.)
       (New usage is discouraged.) $)
    0lno $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> Z e. L ) $=
      ( vx vy vz wcel wa cfv cv co wceq wral cc eqid syl3anc 0oval cnv cba cn0v
      cns cpv 0oo simplll simpllr simplr simprl nvscl simprr nvgcl oveq12d nvsz
      wf oveq2d oveq1d nvzcl nv0rid syl2anc2 3eqtrd eqtr4d ralrimivva ralrimiva
      syl2anc islno mpbir2and ) AUAJZCUAJZKZDBJAUBLZCUBLZDUPGMZHMZAUDLZNZIMZAUE
      LZNZDLZVNVODLZCUDLZNZVRDLZCUELZNZOZIVLPHVLPZGQPACVLVMDVLRZVMRZEUFVKWIGQVK
      VNQJZKZWHHIVLVLWMVOVLJZVRVLJZKZKZWACUCLZWGWQVIVJVTVLJZWAWROVIVJWLWPUGZVIV
      JWLWPUHZWQVIVQVLJZWOWSWTWQVIWLWNXBWTVKWLWPUIZWMWNWOUJZVNVOVPAVLWJVPRZUKSW
      MWNWOULZVQVRAVSVLWJVSRZUMSVTADCVLWRWJWRRZETSWQWGVNWRWCNZWRWFNWRWRWFNZWRWQ
      WDXIWEWRWFWQWBWRVNWCWQVIVJWNWBWROWTXAXDVOADCVLWRWJXHETSUQWQVIVJWOWEWROWTX
      AXFVRADCVLWRWJXHETSUNWQXIWRWRWFWQVJWLXIWROXAXCVNWCCWRWCRZXHUOVFURWQVJWRVM
      JXJWROXACVMWRWKXHUSWRCWFVMWRWKWFRZXHUTVAVBVCVDVEGHIVPWCDAVSWFBCVLVMWJWKXG
      XLXEXKFVGVH $.
  $}

  ${
    $d x z U $.  $d x z W $.  $d x z Z $.
    nmoo0.3 $e |- N = ( U normOpOLD W ) $.
    nmoo0.0 $e |- Z = ( U 0op W ) $.
    $( The operator norm of the zero operator.  (Contributed by NM,
       27-Nov-2007.)  (New usage is discouraged.) $)
    nmoo0 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) ->
         ( N ` Z ) = 0 ) $=
      ( vz vx cnv wcel wa cfv cc0 cxr clt c1 cle wceq wrex eqid csn csup cv wbr
      cnmcv cba cab wf 0oo nmooval mpd3an3 df-sn cn0v nvzcl nvz0 eqbrtrdi fveq2
      wb 0le1 breq1d rspcev syl2anc biantrurd adantr 0oval 3expa ad2antlr eqtrd
      fveq2d eqeq2d anbi2d rexbidva r19.41v bitr2di bitrd abbidv eqtr2id xrltso
      supeq1d wor 0xr supsn mp2an eqtrdi ) AIJZCIJZKZDBLZMUAZNOUBZMWGWHGUCZAUEL
      ZLZPQUDZHUCZWKDLZCUELZLZRZKZGAUFLZSZHUGZNOUBZWJWEWFXACUFLZDUHWHXDRACXAXED
      XATZXETZFUIHGDAWLWQBCXAXEXFXGWLTZWQTZEUJUKWGNXCWIOWGWIWOMRZHUGXCHMULWGXJX
      BHWGXJWNGXASZXJKZXBWEXJXLURWFWEXKXJWEAUMLZXAJXMWLLZPQUDZXKAXAXMXFXMTZUNWE
      XNMPQAWLXMXPXHUOUSUPWNXOGXMXAWKXMRWMXNPQWKXMWLUQUTVAVBVCVDWGXBWNXJKZGXASX
      LWGWTXQGXAWGWKXAJZKZWSXJWNXSWRMWOXSWRCUMLZWQLZMXSWPXTWQWEWFXRWPXTRWKADCXA
      XTXFXTTZFVEVFVIWFYAMRWEXRCWQXTYBXIUOVGVHVJVKVLWNXJGXAVMVNVOVPVQVSVHNOVTMN
      JWJMRVRWANMOWBWCWD $.
  $}

  ${
    0blo.0 $e |- Z = ( U 0op W ) $.
    0blo.7 $e |- B = ( U BLnOp W ) $.
    $( The zero operator is a bounded linear operator.  (Contributed by NM,
       8-Dec-2007.)  (New usage is discouraged.) $)
    0blo $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> Z e. B ) $=
      ( cnv wcel wa clno co cnmoo cfv cr eqid 0lno cc0 nmoo0 0re eqeltrdi
      isblo2 mpbir2and ) BGHCGHIZDAHDBCJKZHDBCLKZMZNHBUDCDEUDOZPUCUFQNBUECDUEOZ
      ERSTADBUDUECUHUGFUAUB $.
  $}

  ${
    $d y z K $.  $d y z M $.  $d x N $.  $d z R $.  $d y z S $.  $d x y z T $.
    $d y z U $.  $d y z W $.  $d x y z X $.  $d y z Y $.  $d x Z $.
    nmlno0.3 $e |- N = ( U normOpOLD W ) $.
    nmlno0.0 $e |- Z = ( U 0op W ) $.
    nmlno0.7 $e |- L = ( U LnOp W ) $.
    ${
      nmlno0lem.u $e |- U e. NrmCVec $.
      nmlno0lem.w $e |- W e. NrmCVec $.
      nmlno0lem.l $e |- T e. L $.
      nmlno0lem.1 $e |- X = ( BaseSet ` U ) $.
      nmlno0lem.2 $e |- Y = ( BaseSet ` W ) $.
      nmlno0lem.r $e |- R = ( .sOLD ` U ) $.
      nmlno0lem.s $e |- S = ( .sOLD ` W ) $.
      nmlno0lem.p $e |- P = ( 0vec ` U ) $.
      nmlno0lem.q $e |- Q = ( 0vec ` W ) $.
      nmlno0lem.k $e |- K = ( normCV ` U ) $.
      nmlno0lem.m $e |- M = ( normCV ` W ) $.
      $( Lemma for ~ nmlno0i .  (Contributed by NM, 28-Nov-2007.)
         (New usage is discouraged.) $)
      nmlno0lem $p |- ( ( N ` T ) = 0 <-> T = Z ) $=
        ( vx vz vy cfv cc0 wceq cv wral wcel wa wne wn c1 cdiv co clt wbr wi cc
        cnv cr nvcl mpan recnd adantr wb nvz fveq2 lno0 eqtrdi biimtrdi necon3d
        mp3an recne0d simpr wo reccld wf lnof ffvelcdmi nvmul0or mp3an1 syl2anc
        imp necon3abid neanior bitr4di mpbir2and nvscl nvgt0 sylancr adantl cle
        mpbid ex wrex cab cxr wss nmosetre mp2an ressxr sstri simpl necon3i nv1
        csup sylan2 1re eqeltrdi w3a 3pm3.2i lnomul eqcomd fveq2d breq1d 2fveq3
        eqle eqeq2d anbi12d rspcev syl12anc eqeq1 anbi2d rexbidv sylibr adantll
        fvex elab wfn ffn ax-mp supxrub nmooval eqeq1i biimpi breqtrd 0re lenlt
        ad2antrr sylancl pm2.65d nne sylib 0oval mp3an12 eqtr4d ralrimiva nmoo0
        0oo eqfnfv impbii ) EJULZUMUNZENUNZUVBUIUOZEULZUVDNULZUNZUILUPZUVCUVBUV
        GUILUVBUVDLUQZURZUVEBUVFUVJUVEBUSZUTUVEBUNZUVJUVKUMVAUVDGULZVBVCZUVEDVC
        ZIULZVDVEZUVIUVKUVQVFUVBUVIUVKUVQUVIUVKURZUVOBUSZUVQUVRUVSUVNUMUSZUVKUV
        RUVMUVIUVMVGUQUVKUVIUVMFVHUQZUVIUVMVIUQRUVDFGLUAUGVJVKVLVMZUVIUVKUVMUMU
        SUVIUVMUMUVEBUVIUVMUMUNZUVDAUNZUVLUWAUVIUWCUWDVNRUVDFGLAUAUEUGVOVKUWDUV
        EAEULZBUVDAEVPUWAKVHUQZEHUQZUWEBUNRSTAEFHKLMBUAUBUEUFQVQWAVRZVSVTWLZWBU
        VIUVKWCUVRUVSUVNUMUNUVLWDZUTUVTUVKURUVRUWJUVOBUVRUVNVGUQZUVEMUQZUVOBUNU
        WJVNZUVRUVMUWBUWIWEZUVIUWLUVKLMUVDEUWAUWFUWGLMEWFZRSTEFHKLMUAUBQWGWAZWH
        VMZUWFUWKUWLUWMSUVNUVEDKMBUBUDUFWIWJWKWMUVNUMUVEBWNWOWPUVRUWFUVOMUQZUVS
        UVQVNSUVRUWKUWLUWRUWNUWQUWFUWKUWLUWRSUVNUVEDKMUBUDWQWJWKZUVOKIMBUBUFUHW
        RWSXBXCWTUVJUVKUVQUTZUVJUVKURZUVPUMXAVEZUWTUXAUVPUJUOZGULZVAXAVEZUKUOZU
        XCEULIULZUNZURZUJLXDZUKXEZXFVDXOZUMXAUVIUVKUVPUXLXAVEZUVBUVRUXKXFXGUVPU
        XKUQZUXMUXKVIXFUWFUWOUXKVIXGSUWPUKUJEGIKLMUBUHXHXIXJXKUVRUXEUVPUXGUNZUR
        ZUJLXDZUXNUVRUVNUVDCVCZLUQZUXRGULZVAXAVEZUVPUXREULZIULZUNZUXQUVRUWKUVIU
        XSUWNUVIUVKXLZUWAUWKUVIUXSRUVNUVDCFLUAUCWQWJWKUVRUXTVIUQUXTVAUNZUYAUVRU
        XTVAVIUVKUVIUVDAUSZUYFUVDAUVEBUWHXMUWAUVIUYGUYFRUVDCFGLAUAUCUEUGXNWJXPZ
        XQXRUYHUXTVAYFWKUVRUVOUYBIUVRUYBUVOUVRUWKUVIUYBUVOUNZUWNUYEUWAUWFUWGXSU
        WKUVIURUYIUWAUWFUWGRSTXTUVNUVDCDEFHKLUAUCUDQYAVKWKYBYCUXPUYAUYDURUJUXRL
        UXCUXRUNZUXEUYAUXOUYDUYJUXDUXTVAXAUXCUXRGVPYDUYJUXGUYCUVPUXCUXRIEYEYGYH
        YIYJUXJUXQUKUVPUVOIYPUXFUVPUNZUXIUXPUJLUYKUXHUXOUXEUXFUVPUXGYKYLYMYQYNU
        XKUVPUUAWSYOUVBUXLUMUNZUVIUVKUVBUYLUVAUXLUMUWAUWFUWOUVAUXLUNRSUWPUKUJEF
        GIJKLMUAUBUGUHOUUBWAUUCUUDUUHUUEUVIUVKUXBUWTVNZUVBUVRUVPVIUQZUMVIUQUYMU
        VRUWFUWRUYNSUWSUVOKIMUBUHVJWSUUFUVPUMUUGUUIYOXBXCUUJUVEBUUKUULUVIUVFBUN
        ZUVBUWAUWFUVIUYORSUVDFNKLBUAUFPUUMUUNWTUUOUUPELYRZNLYRZUVCUVHVNUWOUYPUW
        PLMEYSYTLMNWFZUYQUWAUWFUYRRSFKLMNUAUBPUURXILMNYSYTUILENUUSXIYNUVCUVANJU
        LZUMENJVPUWAUWFUYSUMUNRSFJKNOPUUQXIVRUUT $.
    $}

    ${
      nmlno0i.u $e |- U e. NrmCVec $.
      nmlno0i.w $e |- W e. NrmCVec $.
      $( The norm of a linear operator is zero iff the operator is zero.
         (Contributed by NM, 6-Dec-2007.)  (New usage is discouraged.) $)
      nmlno0i $p |- ( T e. L -> ( ( N ` T ) = 0 <-> T = Z ) ) $=
        ( wcel cfv cc0 wceq wb cn0v cns cnmcv eqid cif fveqeq2 bibi12d cba 0lno
        eqeq1 cnv mp2an elimel nmlno0lem dedth ) ACLZADMNOZAFOZPULAFUAZDMNOZUOF
        OZPAFAUOOUMUPUNUQAUONDUBAUOFUFUCBQMZEQMZBRMZERMZUOBBSMZCESMZDEBUDMZEUDM
        ZFGHIJKAFCBUGLEUGLFCLJKBCEFHIUEUHUIVDTVETUTTVATURTUSTVBTVCTUJUK $.
    $}

    $( The norm of a linear operator is zero iff the operator is zero.
       (Contributed by NM, 24-Nov-2007.)  (New usage is discouraged.) $)
    nmlno0 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) ->
       ( ( N ` T ) = 0 <-> T = Z ) ) $=
      ( wcel cfv cc0 wceq wb wi clno co cnmoo c0o oveq1 cnv caddc cmul cop cabs
      cif eqtrid eleq2d fveq1d eqeq1d eqeq2d bibi12d imbi12d oveq2 eqid elimnvu
      nmlno0i dedth2h 3impia ) BUAJZEUAJZACJZADKZLMZAFMZNZUTVAVBVFOAUTBUBUCUDUE
      UDZUFZEPQZJZAVHERQZKZLMZAVHESQZMZNZOAVHVAEVGUFZPQZJZAVHVQRQZKZLMZAVHVQSQZ
      MZNZOBEVGVGBVHMZVBVJVFVPWFCVIAWFCBEPQVIIBVHEPTUGUHWFVDVMVEVOWFVCVLLWFADVK
      WFDBERQVKGBVHERTUGUIUJWFFVNAWFFBESQVNHBVHESTUGUKULUMEVQMZVJVSVPWEWGVIVRAE
      VQVHPUNUHWGVMWBVOWDWGVLWALWGAVKVTEVQVHRUNUIUJWGVNWCAEVQVHSUNUKULUMAVHVRVT
      VQWCVTUOWCUOVRUOBUPEUPUQURUS $.
  $}

  ${
    $d x A $.  $d x K $.  $d x L $.  $d x M $.  $d x T $.  $d x U $.  $d x W $.
    $d x X $.
    nmlnoubi.1 $e |- X = ( BaseSet ` U ) $.
    nmlnoubi.z $e |- Z = ( 0vec ` U ) $.
    nmlnoubi.k $e |- K = ( normCV ` U ) $.
    nmlnoubi.m $e |- M = ( normCV ` W ) $.
    nmlnoubi.3 $e |- N = ( U normOpOLD W ) $.
    nmlnoubi.7 $e |- L = ( U LnOp W ) $.
    nmlnoubi.u $e |- U e. NrmCVec $.
    nmlnoubi.w $e |- W e. NrmCVec $.
    $( An upper bound for the operator norm of a linear operator, using only
       the properties of nonzero arguments.  (Contributed by NM, 1-Jan-2008.)
       (New usage is discouraged.) $)
    nmlnoubi $p |- ( ( T e. L /\ ( A e. RR /\ 0 <_ A ) /\ A. x e. X ( x =/= Z
     -> ( M ` ( T ` x ) ) <_ ( A x. ( K ` x ) ) ) ) -> ( N ` T ) <_ A ) $=
      ( cc0 wcel cr cle wbr wa cv wne cfv cmul co wral wceq 2fveq3 fveq2 oveq2d
      wi breq12d id imp adantll 0le0 cn0v cnv cba eqid lno0 mp3an12 fveq2d nvz0
      ax-mp eqtrdi adantr oveq2i recn mul01d eqtrid ad2antrl mpbiri pm2.61ne ex
      ralimdv 3impia wf lnof nmoub2i syl3an1 syld3an3 ) CFUAZBUBUAZTBUCUDZUEZAU
      FZKUGZWLCUHGUHZBWLEUHZUIUJZUCUDZUPZAJUKZWQAJUKZCHUHBUCUDZWHWKWSWTWHWKUEZW
      RWQAJXBWRWQXBWRUEWQKCUHZGUHZBKEUHZUIUJZUCUDZWLKWLKULZWNXDWPXFUCWLKGCUMXHW
      OXEBUIWLKEUNUOUQWRWMWQXBWRWMWQWRURUSUTXBXGWRXBXGTTUCUDVAXBXDTXFTUCWHXDTUL
      WKWHXDIVBUHZGUHZTWHXCXIGDVCUAZIVCUAZWHXCXIULRSKCDFIJIVDUHZXILXMVEZMXIVEZQ
      VFVGVHXLXJTULSIGXIXOOVIVJVKVLWIXFTULWHWJWIXFBTUIUJTXETBUIXKXETULRDEKMNVIV
      JVMWIBBVNVOVPVQUQVRVLVSVTWAWBWHJXMCWCZWKWTXAXKXLWHXPRSCDFIJXMLXNQWDVGABCD
      EGHIJXMLXNNOPRSWEWFWG $.
  $}

  ${
    nmlnogt0.3 $e |- N = ( U normOpOLD W ) $.
    nmlnogt0.0 $e |- Z = ( U 0op W ) $.
    nmlnogt0.7 $e |- L = ( U LnOp W ) $.
    $( The norm of a nonzero linear operator is positive.  (Contributed by NM,
       10-Dec-2007.)  (New usage is discouraged.) $)
    nmlnogt0 $p |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) ->
                   ( T =/= Z <-> 0 < ( N ` T ) ) ) $=
      ( cnv wcel w3a cfv cc0 wne clt wbr cba wb eqid nmlno0 necon3bid cxr nmoxr
      wf lnof cle nmooge0 wa wo 0xr xrlttri2 mpan2 adantr wn xrlenlt mpan biorf
      biimpa syl bitr4d syl2anc syld3an3 bitr3d ) BJKZEJKZACKZLZADMZNOZAFONVIPQ
      ZVHVINAFABCDEFGHIUAUBVEVFVGBRMZERMZAUEZVJVKSZABCEVLVMVLTZVMTZIUFVEVFVNLVI
      UCKZNVIUGQZVOABDEVLVMVPVQGUDABDEVLVMVPVQGUHVRVSUIZVJVINPQZVKUJZVKVRVJWBSZ
      VSVRNUCKZWCUKVINULUMUNVTWAUOZVKWBSVRVSWEWDVRVSWESUKNVIUPUQUSWAVKURUTVAVBV
      CVD $.
  $}

  ${
    $d x L $.  $d x T $.  $d x U $.  $d x W $.  $d x X $.
    lnon0.1 $e |- X = ( BaseSet ` U ) $.
    lnon0.6 $e |- Z = ( 0vec ` U ) $.
    lnon0.0 $e |- O = ( U 0op W ) $.
    lnon0.7 $e |- L = ( U LnOp W ) $.
    $( The domain of a nonzero linear operator contains a nonzero vector.
       (Contributed by NM, 15-Dec-2007.)  (New usage is discouraged.) $)
    lnon0 $p |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\ T =/= O )
                   -> E. x e. X x =/= Z ) $=
      ( cnv wcel wne wn wceq wral bitr3i cfv w3a cv wrex ralnex nne ralbii cn0v
      csn cxp wfn wa fveq2 cba eqid lno0 sylan9eqr ralimdv lnof jctild fconstfv
      ex ffnd wf fvex fconst2 imbitrdi 0ofval 3adant3 sylibrd biimtrid necon1ad
      eqeq2d imp ) CMNZFMNZBDNZUAZBEOAUBZHOZAGUCZVQVTBEVTPZVRHQZAGRZVQBEQZWAVSP
      ZAGRWCVSAGUDWEWBAGVRHUEUFSVQWCBGFUGTZUHZUIZQZWDVQWCBGUJZVRBTZWFQZAGRZUKZW
      IVQWCWMWJVQWBWLAGVQWBWLWBVQWKHBTWFVRHBULHBCDFGFUMTZWFIWOUNZJWFUNZLUOUPVAU
      QVQGWOBBCDFGWOIWPLURVBUSWNGWGBVCWIAGWFBUTGWFBFUGVDVESVFVQEWHBVNVOEWHQVPCE
      FGWFIWQKVGVHVLVIVJVKVM $.
  $}

  ${
    nmblolbi.1 $e |- X = ( BaseSet ` U ) $.
    nmblolbi.4 $e |- L = ( normCV ` U ) $.
    nmblolbi.5 $e |- M = ( normCV ` W ) $.
    nmblolbi.6 $e |- N = ( U normOpOLD W ) $.
    nmblolbi.7 $e |- B = ( U BLnOp W ) $.
    nmblolbi.u $e |- U e. NrmCVec $.
    nmblolbi.w $e |- W e. NrmCVec $.
    ${
      nmblolbii.b $e |- T e. B $.
      $( A lower bound for the norm of a bounded linear operator.  (Contributed
         by NM, 7-Dec-2007.)  (New usage is discouraged.) $)
      nmblolbii $p |- ( A e. X ->
                ( M ` ( T ` A ) ) <_ ( ( N ` T ) x. ( L ` A ) ) ) $=
        ( wcel cfv cc0 cmul co cle wbr cn0v wceq fveq2 fveq2d oveq2d breq12d wa
        wne cdiv c1 cns cr cba cnv nvcl mpan adantr eqid nvz necon3bid rereccld
        wb biimpar clt nvgt0 biimpa recgt0d 0re ltle sylancr mpd blof ffvelcdmi
        wi wf mp3an nvsge0 mp3an1 syl21anc cc recnd simpl clno w3a bloln lnomul
        3pm3.2i syl2anc divrec2d 3eqtr4rd ancoms syldan nv1 eqle nmoolb eqbrtrd
        nvscl nmblore a1i ledivmul2 syl112anc mpbid 0le0 lno0 fveq2i nvz0 ax-mp
        eqtri oveq2i recni mul01i 3brtr4i pm2.61ne ) AIRZACSZFSZCGSZAESZUAUBZUC
        UDZDUESZCSZFSZYAYEESZUAUBZUCUDZAYEAYEUFZXTYGYCYIUCYKXSYFFAYECUGUHYKYBYH
        YAUAAYEEUGUIUJXRAYEULZUKZXTYBUMUBZYAUCUDZYDYMYNUNYBUMUBZADUOSZUBZCSZFSZ
        YAUCYMYPXSHUOSZUBZFSZYPXTUAUBZYTYNYMYPUPRZTYPUCUDZXSHUQSZRZUUCUUDUFZYMY
        BXRYBUPRZYLDURRZXRUUJOADEIJKUSUTVAZXRYBTULYLXRYBTAYEUUKXRYBTUFYKVFOADEI
        YEJYEVBZKVCUTVDVGZVEZYMTYPVHUDZUUFYMYBUULXRYLTYBVHUDZUUKXRYLUUQVFOADEIY
        EJUUMKVIUTVJZVKYMTUPRUUEUUPUUFVRVLUUOTYPVMVNVOXRUUHYLIUUGACUUKHURRZCBRZ
        IUUGCVSZOPQBCDHIUUGJUUGVBZNVPVTZVQZVAUUSUUEUUFUKUUHUUIPYPXSUUAHFUUGUVBU
        UAVBZLWAWBWCYMYSUUBFYMYPWDRZXRYSUUBUFZYMYPUUOWEZXRYLWFUUKUUSCDHWGUBZRZW
        HUVFXRUKUVGUUKUUSUVJOPUUKUUSUUTUVJOPQBCDUVIHUVIVBZNWIVTZWKYPAYQUUACDUVI
        HIJYQVBZUVEUVKWJUTWLUHYMXTYBYMXTXRXTUPRZYLXRUUSUUHUVNPUVDXSHFUUGUVBLUSV
        NVAZWEYMYBUULWEUUNWMWNYMYRIRZYRESZUNUCUDZYTYAUCUDZXRYLUVFUVPUVHUVFXRUVP
        UUKUVFXRUVPOYPAYQDIJUVMXAWBWOWPZYMUVQUPRZUVQUNUFZUVRYMUUKUVPUWAOUVTYRDE
        IJKUSVNUUKXRYLUWBOAYQDEIYEJUVMUUMKWQWBUVQUNWRWLUUKUUSUVAWHUVPUVRUKUVSUU
        KUUSUVAOPUVCWKYRCDEFGHIUUGJUVBKLMWSUTWLWTYMUVNYAUPRZUUJUUQYOYDVFUVOUWCY
        MUUKUUSUUTUWCOPQBCDGHIUUGJUVBMNXBVTZXCUULUURXTYAYBXDXEXFYJXRTTYGYIUCXGY
        GHUESZFSZTYFUWEFUUKUUSUVJYFUWEUFOPUVLYECDUVIHIUUGUWEJUVBUUMUWEVBZUVKXHV
        TXIUUSUWFTUFPHFUWEUWGLXJXKXLYIYATUAUBTYHTYAUAUUKYHTUFODEYEUUMKXJXKXMYAY
        AUWDXNXOXLXPXCXQ $.
    $}

    $( A lower bound for the norm of a bounded linear operator.  (Contributed
       by NM, 10-Dec-2007.)  (New usage is discouraged.) $)
    nmblolbi $p |- ( ( T e. B /\ A e. X ) ->
              ( M ` ( T ` A ) ) <_ ( ( N ` T ) x. ( L ` A ) ) ) $=
      ( wcel cfv cmul co cle wbr c0o cif wceq fveq1 fveq2d fveq2 oveq1d breq12d
      wi imbi2d cnv eqid 0blo mp2an elimel nmblolbii dedth imp ) CBQZAIQZACRZFR
      ZCGRZAERZSTZUAUBZVAVBVHUKVBAVACDHUCTZUDZRZFRZVJGRZVFSTZUAUBZUKCVICVJUEZVH
      VOVBVPVDVLVGVNUAVPVCVKFACVJUFUGVPVEVMVFSCVJGUHUIUJULABVJDEFGHIJKLMNOPCVIB
      DUMQHUMQVIBQOPBDHVIVIUNNUOUPUQURUSUT $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x L $.  $d x y M $.  $d x y N $.  $d x y T $.
    $d x y U $.  $d x y W $.  $d x y X $.
    isblo3i.1 $e |- X = ( BaseSet ` U ) $.
    isblo3i.m $e |- M = ( normCV ` U ) $.
    isblo3i.n $e |- N = ( normCV ` W ) $.
    isblo3i.4 $e |- L = ( U LnOp W ) $.
    isblo3i.5 $e |- B = ( U BLnOp W ) $.
    isblo3i.u $e |- U e. NrmCVec $.
    isblo3i.w $e |- W e. NrmCVec $.
    $( The predicate "is a bounded linear operator."  Definition 2.7-1 of
       [Kreyszig] p. 91.  (Contributed by NM, 11-Dec-2007.)
       (New usage is discouraged.) $)
    isblo3i $p |- ( T e. B <-> ( T e. L /\
          E. x e. RR A. y e. X ( N ` ( T ` y ) ) <_ ( x x. ( M ` y ) ) ) ) $=
      ( wcel cfv cr cv cmul co cle wbr wral wrex wa cnv bloln mp3an12 cnmoo cba
      eqid nmblore nmblolbi ralrimiva wceq oveq1 breq2d ralbidv syl2anc jca w3a
      rspcev cpnf clt simp1 wf lnof cabs cxr nmoxr 3ad2ant1 recn rexrd 3ad2ant2
      abscld pnfxr a1i nmoub3i ltpnf syl xrlelttrd syl3an1 isblo mp2an sylanbrc
      wb rexlimdv3a imp impbii ) DCRZDFRZBUAZDSHSZAUAZWOGSZUBUCZUDUEZBJUFZATUGZ
      UHWMWNXBEUIRZIUIRZWMWNPQCDEFINOUJUKWMDEIULUCZSZTRZWPXFWRUBUCZUDUEZBJUFZXB
      XCXDWMXGPQCDEXEIJIUMSZKXKUNZXEUNZOUOUKWMXIBJWOCDEGHXEIJKLMXMOPQUPUQXAXJAX
      FTWQXFURZWTXIBJXNWSXHWPUDWQXFWRUBUSUTVAVEVBVCWNXBWMWNXAWMATWNWQTRZXAVDWNX
      FVFVGUEZWMWNXOXAVHWNJXKDVIZXOXAXPXCXDWNXQPQDEFIJXKKXLNVJUKXQXOXAVDZXFWQVK
      SZVFXQXOXFVLRZXAXCXDXQXTPQDEXEIJXKKXLXMVMUKVNXOXQXSVLRXAXOXSXOWQWQVOVRZVP
      VQVFVLRXRVSVTBWQDEGHXEIJXKKXLLMXMPQWAXOXQXSVFVGUEZXAXOXSTRYBYAXSWBWCVQWDW
      EXCXDWMWNXPUHWIPQCDEFXEIXMNOWFWGWHWJWKWL $.

    $( Properties that determine a bounded linear operator.  (Contributed by
       NM, 13-Jan-2008.)  (New usage is discouraged.) $)
    blo3i $p |- ( ( T e. L /\ A e. RR /\ A. y e. X ( N ` ( T ` y ) ) <_
               ( A x. ( M ` y ) ) ) -> T e. B ) $=
      ( vx wcel cr cv cfv cmul co cle wbr wral wa wrex wceq oveq1 breq2d rspcev
      ralbidv isblo3i biimpri sylan2 3impb ) DFSZBTSZAUAZDUBHUBZBVAGUBZUCUDZUEU
      FZAJUGZDCSZUTVFUHUSVBRUAZVCUCUDZUEUFZAJUGZRTUIZVGVKVFRBTVHBUJZVJVEAJVMVIV
      DVBUEVHBVCUCUKULUNUMVGUSVLUHRACDEFGHIJKLMNOPQUOUPUQUR $.
  $}

  ${
    blometi.1 $e |- X = ( BaseSet ` U ) $.
    blometi.2 $e |- Y = ( BaseSet ` W ) $.
    blometi.8 $e |- C = ( IndMet ` U ) $.
    blometi.d $e |- D = ( IndMet ` W ) $.
    blometi.6 $e |- N = ( U normOpOLD W ) $.
    blometi.7 $e |- B = ( U BLnOp W ) $.
    blometi.u $e |- U e. NrmCVec $.
    blometi.w $e |- W e. NrmCVec $.
    $( Upper bound for the distance between the values of a bounded linear
       operator.  (Contributed by NM, 11-Dec-2007.)
       (New usage is discouraged.) $)
    blometi $p |- ( ( T e. B /\ P e. X /\ Q e. X ) ->
         ( ( T ` P ) D ( T ` Q ) ) <_ ( ( N ` T ) x. ( P C Q ) ) ) $=
      ( cfv wcel w3a cnsb co cnmcv cmul cle wbr wa cnv eqid nvmcl mp3an1 sylan2
      nmblolbi 3impb wceq wf mp3an12 ffvelcdmda 3adant3 3adant2 imsdval syl2anc
      bloln lnosub mp3anl1 mpanl1 syl3an1 fveq2d eqtr4d 3adant1 oveq2d 3brtr4d
      blof clno ) FAUAZDJUAZEJUAZUBZDEGUCTZUDZFTZIUETZTZFHTZWBGUETZTZUFUDZDFTZE
      FTZCUDZWFDEBUDZUFUDUGVQVRVSWEWIUGUHZVRVSUIZVQWBJUAZWNGUJUAZVRVSWPRDEGWAJL
      WAUKZULUMWBAFGWGWDHIJLWGUKZWDUKZPQRSUOUNUPVTWLWJWKIUCTZUDZWDTZWEVTWJKUAZW
      KKUAZWLXCUQZVQVRXDVSVQJKDFWQIUJUAZVQJKFURRSAFGIJKLMQVOUSZUTVAVQVSXEVRVQJK
      EFXHUTVBXGXDXEXFSWJWKCIXAWDKMXAUKZWTOVCUMVDVTWCXBWDVQFGIVPUDZUAZVRVSWCXBU
      QZWQXGVQXKRSAFGXJIXJUKZQVEUSXKVRVSXLXGXKWOXLSWQXGXKWOXLRDEFGXJWAXAIJLWRXI
      XMVFVGVHUPVIVJVKVTWMWHWFUFVRVSWMWHUQZVQWQVRVSXNRDEBGWAWGJLWRWSNVCUMVLVMVN
      $.
  $}

  ${
    $d w x y z B $.  $d w x y z C $.  $d w x y z D $.  $d x L $.  $d x y z P $.
    $d w x y z J $.  $d w x y z K $.  $d w x y z T $.  $d w x y z U $.
    $d w x y z W $.  $d x y z X $.
    blocni.8 $e |- C = ( IndMet ` U ) $.
    blocni.d $e |- D = ( IndMet ` W ) $.
    blocni.j $e |- J = ( MetOpen ` C ) $.
    blocni.k $e |- K = ( MetOpen ` D ) $.
    blocni.4 $e |- L = ( U LnOp W ) $.
    blocni.5 $e |- B = ( U BLnOp W ) $.
    blocni.u $e |- U e. NrmCVec $.
    blocni.w $e |- W e. NrmCVec $.
    blocni.l $e |- T e. L $.
    ${
      blocnilem.1 $e |- X = ( BaseSet ` U ) $.
      $( TODO - this needs to be broken up or shortened $)
      $( Lemma for ~ blocni and ~ lnocni .  If a linear operator is continuous
         at any point, it is bounded.  (Contributed by NM, 17-Dec-2007.)
         (Revised by Mario Carneiro, 10-Jan-2014.)
         (New usage is discouraged.) $)
      blocnilem $p |- ( ( P e. X /\ T e. ( ( J CnP K ) ` P ) ) -> T e. B ) $=
        ( vz vx vy wcel ccnp co cfv wa cv cnmcv cmul cle wbr wral cr wrex c1 wi
        crp cxmet cba cnv imsxmet eqid 1rp metcnpi3 mpanr2 mpanl12 cdiv rpreccl
        ax-mp rpred ad2antlr cnsb wb wceq imsdval mp3an1 breq1d mp3an ffvelcdmi
        wf lnof syl2an 3pm3.2i lnosub mpan fveq2d eqtr4d imbi12d ancoms adantlr
        w3a ralbidva cn0v 2fveq3 fveq2 oveq2d breq12d wne cns cpv a1i simpll cc
        simpr nvcl adantr cc0 clt nvgt0 biimpa elrpd rpdivcl rpcnd simprl nvscl
        syl3anc nvpncan2 rprege0d nvsge0 rpcn ad2antrl recnd nvz biimpar adantl
        necon3bid divcan1d 3eqtrd rpre fvoveq1 syl syl2anc eqtrd rpcnne0 breq2d
        imp nvz0 leidd eqbrtrd nvgcl mpid sylancr 1red lemuldiv2d lnomul recdiv
        rspcv rpne0 divrec2d eqtr2d 3bitr4d sylibd an32s lno0 fveq2i eqtri 0le0
        anassrs eqbrtri oveq2i mul01 eqtrid breqtrrid ad3antlr ralrimdva sylbid
        pm2.61ne ex oveq1 ralbidv rspcev rexlimdva2 syl5 isblo3i mpbiran sylibr
        ) DKUEZEDGHUFUGUHUEZUIUBUJZEUHZJUKUHZUHZUCUJZUWBFUKUHZUHZULUGZUMUNZUBKU
        OZUCUPUQZEAUEZUVTUWAUWLUWAUWFDBUGZUDUJZUMUNZUWFEUHZDEUHZCUGZURUMUNZUSZU
        CKUOZUDUTUQZUVTUWLBKVAUHUEZCJVBUHZVAUHUEZUWAUXCFVCUEZUXDRBFKUALVDVLJVCU
        EZUXFSCJUXEUXEVEZMVDVLUXDUXFUIUWAURUTUEUXCVFUDUCURBCDEGHKUXENOVGVHVIUVT
        UXBUWLUDUTUVTUWOUTUEZUIZUXBUIURUWOVJUGZUPUEZUWEUXLUWHULUGZUMUNZUBKUOZUW
        LUXJUXMUVTUXBUXJUXLUWOVKZVMVNUXKUXBUXPUXKUXBUWFDFVOUHZUGZUWGUHZUWOUMUNZ
        UXSEUHZUWDUHZURUMUNZUSZUCKUOZUXPUXKUXAUYEUCKUVTUWFKUEZUXAUYEVPZUXJUYGUV
        TUYHUYGUVTUIZUWPUYAUWTUYDUYIUWNUXTUWOUMUXGUYGUVTUWNUXTVQRUWFDBFUXRUWGKU
        AUXRVEZUWGVEZLVRVSVTUYIUWSUYCURUMUYIUWSUWQUWRJVOUHZUGZUWDUHZUYCUYGUWQUX
        EUEZUWRUXEUEZUWSUYNVQZUVTKUXEUWFEUXGUXHEIUEZKUXEEWCRSTEFIJKUXEUAUXIPWDW
        AZWBKUXEDEUYSWBUXHUYOUYPUYQSUWQUWRCJUYLUWDUXEUXIUYLVEZUWDVEZMVRVSWEUYIU
        YBUYMUWDUXGUXHUYRWNZUYIUYBUYMVQUXGUXHUYRRSTWFZUWFDEFIUXRUYLJKUAUYJUYTPW
        GWHWIWJVTWKWLWMWOUXKUYFUXOUBKUXKUWBKUEZUIZUYFUXOVUEUYFUIUXOFWPUHZEUHZUW
        DUHZUXLVUFUWGUHZULUGZUMUNZUWBVUFUWBVUFVQZUWEVUHUXNVUJUMUWBVUFUWDEWQVULU
        WHVUIUXLULUWBVUFUWGWRWSWTVUEUWBVUFXAZUYFUXOVUEVUMUIUYFUXOUXKVUDVUMUYFUX
        OUSUXKVUDVUMUIZUIZUYFDUWOUWHVJUGZUWBFXBUHZUGZFXCUHZUGZDUXRUGZEUHZUWDUHZ
        URUMUNZUXOVUOUYFVVAUWGUHZUWOUMUNZVVDVUOVVEUWOUWOUMVUOVVEVURUWGUHZVUPUWH
        ULUGZUWOVUOVVAVURUWGVUOUXGUVTVURKUEZVVAVURVQUXGVUORXDZUVTUXJVUNXEZVUOUX
        GVUPXFUEZVUDVVIVVJVUOVUPUXKUXJUWHUTUEZVUPUTUEVUNUVTUXJXGZVUNUWHVUDUWHUP
        UEZVUMUXGVUDVVORUWBFUWGKUAUYKXHWHZXIVUDVUMXJUWHXKUNZUXGVUDVUMVVQVPRUWBF
        UWGKVUFUAVUFVEZUYKXLWHXMXNZUWOUWHXOWEZXPZUXKVUDVUMXQZVUPUWBVUQFKUAVUQVE
        ZXRXSZDVURFVUSUXRKUAVUSVEZUYJXTXSZWIVUOUXGVUPUPUEXJVUPUMUNUIZVUDVVGVVHV
        QVVJVUOVUPVVTYAZVWBVUPUWBVUQFUWGKUAVWCUYKYBXSVUOUWOUWHUXJUWOXFUEZUVTVUN
        UWOYCVNZVUOUWHVUDVVOUXKVUMVVPYDYEZVUNUWHXJXAZUXKVUDVWLVUMVUDUWHXJUWBVUF
        UXGVUDUWHXJVQVULVPRUWBFUWGKVUFUAVVRUYKYFWHYIYGYHYJYKUXJUWOUWOUMUNUVTVUN
        UXJUWOUWOYLUUAVNUUBVUOVUTKUEZUYFVVFVVDUSZUSVUOUXGUVTVVIVWMVVJVVKVWDDVUR
        FVUSKUAVWEUUCXSUYEVWNUCVUTKUWFVUTVQZUYAVVFUYDVVDVWOUXTVVEUWOUMUWFVUTDUW
        GUXRYMVTVWOUYCVVCURUMVWOUYBVVBUWDUWFVUTDEUXRYMWIVTWKUUJYNUUDVUOVUPUWEUL
        UGZURUMUNUWEURVUPVJUGZUMUNVVDUXOVUOUWEURVUPVUDUWEUPUEZUXKVUMVUDUXHUWCUX
        EUEZVWRSKUXEUWBEUYSWBZUWCJUWDUXEUXIVUAXHUUEYDVUOUUFVVTUUGVUOVVCVWPURUMV
        UOVVCVUPUWCJXBUHZUGZUWDUHZVWPVUOVVBVXBUWDVUOVVBVUREUHZVXBVUOVVAVUREVWFW
        IVUOVVLVUDVXDVXBVQZVWAVWBVUBVVLVUDUIVXEVUCVUPUWBVUQVXAEFIJKUAVWCVXAVEZP
        UUHWHYOYPWIVUOUXHVWGVWSVXCVWPVQUXHVUOSXDVWHVUDVWSUXKVUMVWTYDVUPUWCVXAJU
        WDUXEUXIVXFVUAYBXSYPVTVUOUXNVWQUWEUMVUOVWQUWHUWOVJUGZUXNUXKUXJVVMVWQVXG
        VQZVUNVVNVVSUXJVWIUWOXJXAZUIUWHXFUEVWLUIVXHVVMUWOYQUWHYQUWOUWHUUIWEWEVU
        OUWHUWOVWKVWJUXJVXIUVTVUNUWOUUKVNUULUUMYRUUNUUOUVAYSUUPUXJVUKUVTVUDUYFU
        XJVUHXJVUJUMVUHXJXJUMVUHJWPUHZUWDUHZXJVUGVXJUWDUXGUXHUYRVUGVXJVQRSTVUFE
        FIJKUXEVXJUAUXIVVRVXJVEZPUUQWAUURUXHVXKXJVQSJUWDVXJVXLVUAYTVLUUSUUTUVBU
        XJUXLXFUEZVUJXJVQUXJUXLUXQXPVXMVUJUXLXJULUGXJVUIXJUXLULUXGVUIXJVQRFUWGV
        UFVVRUYKYTVLUVCUXLUVDUVEYNUVFUVGUVJUVKUVHUVIYSUWKUXPUCUXLUPUWFUXLVQZUWJ
        UXOUBKVXNUWIUXNUWEUMUWFUXLUWHULUVLYRUVMUVNYOUVOUVPYSUWMUYRUWLTUCUBAEFIU
        WGUWDJKUAUYKVUAPQRSUVQUVRUVS $.
    $}

    $( A linear operator is continuous iff it is bounded.  Theorem 2.7-9(a) of
       [Kreyszig] p. 97.  (Contributed by NM, 18-Dec-2007.)  (Revised by Mario
       Carneiro, 10-Jan-2014.)  (New usage is discouraged.) $)
    blocni $p |- ( T e. ( J Cn K ) <-> T e. B ) $=
      ( wcel cfv vx vw vz vy ccn co cn0v cba ccnp eqid nvzcl ax-mp cxmet ctopon
      cnv imsmet metxmet mopntopon toponunii cncnpi mpan2 blocnilem sylancr c0o
      cmet eleq1 wne wa wf cv clt wbr wi wral crp wrex cnmoo cdiv simprr cr cc0
      nmblore mp3an12 nmlnogt0 mp3an biimpi anim12i elrp sylibr adantr rpdivcld
      wb simprl metcl mp3an1 sylan simplrr rpred ad2antrr ltmuldiv2 syl3anc cle
      cmul id ad2ant2r blometi 3expa ffvelcdmi syl2an remulcl adantllr adantlrr
      anassrs lelttr mpand sylbird ralrimiva breq2 rspceaimv syl2anc ralrimivva
      lnof jctil metcn csn cxp wceq 0ofval cnconst2 eqeltri a1i pm2.61ne impbii
      mp2an ) DFGUEUFZSZDASZYPEUGTZEUHTZSZDYRFGUIUFTSZYQEUOSZYTPEYSYRYSUJZYRUJU
      KULZYPYTUUAUUDYRDFGYSYSFBYSUMTSZFYSUNTSZBYSVETSZUUEUUBUUGPBEYSUUCJUPULZBY
      SUQULZBFYSLURULZUSUTVAABCYRDEFGHIYSJKLMNOPQRUUCVBVCYQYPEIVDUFZYOSZDUUKDUU
      KYOVFYQDUUKVGZVHZYSIUHTZDVIZUAVJZUBVJZBUFZUCVJZVKVLZUUQDTZUURDTZCUFZUDVJZ
      VKVLZVMUBYSVNUCVOVPZUDVOVNUAYSVNZVHZYPUUNUVHUUPUUNUVGUAUDYSVOUUNUUQYSSZUV
      EVOSZVHZVHZUVEDEIVQUFZTZVRUFZVOSUUSUVPVKVLZUVFVMZUBYSVNUVGUVMUVEUVOUUNUVJ
      UVKVSUUNUVOVOSZUVLUUNUVOVTSZWAUVOVKVLZVHZUVSYQUVTUUMUWAUUBIUOSZYQUVTPQADE
      UVNIYSUUOUUCUUOUJZUVNUJZOWBWCZUUMUWAUUBUWCDHSZUUMUWAWLPQRDEHUVNIUUKUWEUUK
      UJZNWDWEWFWGZUVOWHWIWJWKUVMUVRUBYSUVMUURYSSZVHZUVQUVOUUSXCUFZUVEVKVLZUVFU
      WKUUSVTSZUVEVTSZUWBUWMUVQWLUVMUVJUWJUWNUUNUVJUVKWMZUUGUVJUWJUWNUUHUUQUURB
      YSWNWOZWPUWKUVEUUNUVJUVKUWJWQWRZUUNUWBUVLUWJUWIWSUUSUVEUVOWTXAUWKUVDUWLXB
      VLZUWMUVFUVMYQUVJVHZUWJUWSYQUVJUWTUUMUVKUWTXDXEYQUVJUWJUWSABCUUQUURDEUVNI
      YSUUOUUCUWDJKUWEOPQXFXGWPUWKUVDVTSZUWLVTSZUWOUWSUWMVHUVFVMUVMUVJUWJUXAUWP
      UVJUVBUUOSZUVCUUOSZUXAUWJYSUUOUUQDUUBUWCUWGUUPPQRDEHIYSUUOUUCUWDNYBWEZXHY
      SUUOUURDUXEXHCUUOVETSZUXCUXDUXAUWCUXFQCIUUOUWDKUPULZUVBUVCCUUOWNWOXIWPUUN
      UVJUWJUXBUVKYQUVJUWJUXBUUMYQUVJUWJUXBYQUVTUWNUXBUVJUWJVHUWFUWQUVOUUSXJXIX
      MXKXLUWRUVDUWLUVEXNXAXOXPXQUVAUVQUVFUCUBUVPVOYSUUTUVPUUSVKXRXSXTYAUXEYCUU
      ECUUOUMTSZYPUVIWLUUIUXFUXHUXGCUUOUQULZUAUDUCUBBCDFGYSUUOLMYDYNWIUULYQUUKY
      SIUGTZYEYFZYOUUBUWCUUKUXKYGPQEUUKIYSUXJUUCUXJUJZUWHYHYNUUFGUUOUNTSZUXJUUO
      SZUXKYOSUUJUXHUXMUXICGUUOMURULUWCUXNQIUUOUXJUWDUXLUKULUXJFGYSUUOYIWEYJYKY
      LYM $.

    ${
      lnocni.1 $e |- X = ( BaseSet ` U ) $.
      $( If a linear operator is continuous at any point, it is continuous
         everywhere.  Theorem 2.7-9(b) of [Kreyszig] p. 97.  (Contributed by
         NM, 18-Dec-2007.)  (New usage is discouraged.) $)
      lnocni $p |- ( ( P e. X /\ T e. ( ( J CnP K ) ` P ) ) ->
                T e. ( J Cn K ) ) $=
        ( wcel ccnp co cfv wa ccn blocnilem blocni sylibr ) DKUBEDGHUCUDUEUBUFE
        AUBEGHUGUDUBABCDEFGHIJKLMNOPQRSTUAUHABCEFGHIJLMNOPQRSTUIUJ $.
    $}
  $}

  ${
    blocn.8 $e |- C = ( IndMet ` U ) $.
    blocn.d $e |- D = ( IndMet ` W ) $.
    blocn.j $e |- J = ( MetOpen ` C ) $.
    blocn.k $e |- K = ( MetOpen ` D ) $.
    blocn.5 $e |- B = ( U BLnOp W ) $.
    blocn.u $e |- U e. NrmCVec $.
    blocn.w $e |- W e. NrmCVec $.
    ${
      blocn.4 $e |- L = ( U LnOp W ) $.
      $( A linear operator is continuous iff it is bounded.  Theorem 2.7-9(a)
         of [Kreyszig] p. 97.  (Contributed by NM, 25-Dec-2007.)
         (New usage is discouraged.) $)
      blocn $p |- ( T e. L -> ( T e. ( J Cn K ) <-> T e. B ) ) $=
        ( wcel co wb ccn c0o cif wceq eleq1 bibi12d cnv eqid 0lno elimel blocni
        mp2an dedth ) DHRZDFGUASZRZDARZTUNDEIUBSZUCZUORZUSARZTDURDUSUDUPUTUQVAD
        USUOUEDUSAUEUFABCUSEFGHIJKLMQNOPDURHEUGRIUGRURHROPEHIURURUHQUIULUJUKUM
        $.
    $}

    $( A bounded linear operator is continuous.  (Contributed by NM,
       25-Dec-2007.)  (New usage is discouraged.) $)
    blocn2 $p |- ( T e. B -> T e. ( J Cn K ) ) $=
      ( clno co wcel ccn cnv eqid bloln mp3an12 blocn biimprd mpcom ) DEHPQZRZD
      ARZDFGSQRZETRHTRUIUHNOADEUGHUGUAZMUBUCUHUJUIABCDEFGUGHIJKLMNOUKUDUEUF $.
  $}

  ${
    $d u w P $.  $d s t u w x y U $.  $d s t u w x y W $.  $d s t u w x X $.
    $d u w Q $.  $d s t u w y Y $.
    ajfval.1 $e |- X = ( BaseSet ` U ) $.
    ajfval.2 $e |- Y = ( BaseSet ` W ) $.
    ajfval.3 $e |- P = ( .iOLD ` U ) $.
    ajfval.4 $e |- Q = ( .iOLD ` W ) $.
    ajfval.5 $e |- A = ( U adj W ) $.
    $( The adjoint function.  (Contributed by NM, 25-Jan-2008.)  (Revised by
       Mario Carneiro, 16-Nov-2013.)  (New usage is discouraged.) $)
    ajfval $p |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> A =
     { <. t , s >. | ( t : X --> Y /\ s : Y --> X /\ A. x e. X A. y e. Y
    ( ( t ` x ) Q y ) = ( x P ( s ` y ) ) ) } ) $=
      ( co cv cfv cba vu vw cnv wcel wa caj wf wceq wral w3a copab cdip eqtr4di
      fveq2 feq2d feq3d oveqd eqeq2d ralbidv raleqbidv 3anbi123d opabbidv df-aj
      eqeq1d cmap cxp ovex xpex fvexi anbi12i biimpri 3adant3 ssopab2i sseqtrri
      elmap df-xp ssexi ovmpo eqtrid ) GUCUDHUCUDUEDGHUFQIJCRZUGZJIKRZUGZARZVTS
      ZBRZFQZWDWFWBSZEQZUHZBJUIZAIUIZUJZCKUKZPUAUBGHUCUCUARZTSZUBRZTSZVTUGZWRWP
      WBUGZWEWFWQULSZQZWDWHWOULSZQZUHZBWRUIZAWPUIZUJZCKUKWNUFIWRVTUGZWRIWBUGZXB
      WIUHZBWRUIZAIUIZUJZCKUKWOGUHZXHXNCKXOWSXIWTXJXGXMXOWPIWRVTXOWPGTSIWOGTUNL
      UMZUOXOWPIWBWRXPUPXOXFXLAWPIXPXOXEXKBWRXOXDWIXBXOXCEWDWHXOXCGULSEWOGULUNN
      UMUQURUSUTVAVBWQHUHZXNWMCKXQXIWAXJWCXMWLXQWRJVTIXQWRHTSJWQHTUNMUMZUPXQWRJ
      IWBXRUOXQXLWKAIXQXKWJBWRJXRXQXBWGWIXQXAFWEWFXQXAHULSFWQHULUNOUMUQVDUTUSVA
      VBABUBUACKVCWNJIVEQZIJVEQZVFZXSXTJIVEVGIJVEVGVHWNVTXSUDZWBXTUDZUEZCKUKYAW
      MYDCKWAWCYDWLYDWAWCUEYBWAYCWCJIVTJHTMVIZIGTLVIZVOIJWBYFYEVOVJVKVLVMCKXSXT
      VPVNVQVRVS $.
  $}

  ${
    $d t u A $.  $d t T $.  $d t u U $.
    hmoval.8 $e |- H = ( HmOp ` U ) $.
    hmoval.9 $e |- A = ( U adj U ) $.
    $( The set of Hermitian (self-adjoint) operators on a normed complex vector
       space.  (Contributed by NM, 26-Jan-2008.)  (Revised by Mario Carneiro,
       16-Nov-2013.)  (New usage is discouraged.) $)
    hmoval $p |- ( U e. NrmCVec -> H = { t e. dom A | ( A ` t ) = t } ) $=
      ( vu cnv wcel chmo cfv cv wceq cdm crab caj co oveq12 anidms eqtr4di ovex
      dmeqd fveq1d eqeq1d rabeqbidv df-hmo cvv eqeltri dmex rabex fvmpt eqtrid
      ) CHIDCJKALZBKZUMMZABNZOZEGCUMGLZURPQZKZUMMZAUSNZOUQHJURCMZVAUOAVBUPVCUSB
      VCUSCCPQZBVCUSVDMURCURCPRSFTZUBVCUTUNUMVCUMUSBVEUCUDUEGAUFUOAUPBBVDUGFCCP
      UAUHUIUJUKUL $.

    $( The predicate "is a hermitian operator."  (Contributed by NM,
       26-Jan-2008.)  (New usage is discouraged.) $)
    ishmo $p |- ( U e. NrmCVec ->
      ( T e. H <-> ( T e. dom A /\ ( A ` T ) = T ) ) ) $=
      ( vt cnv wcel cv cfv wceq cdm crab wa hmoval eleq2d fveq2 id eqeq12d
      elrab bitrdi ) CHIZBDIBGJZAKZUDLZGAMZNZIBUGIBAKZBLZOUCDUHBGACDEFPQUFUJGBU
      GUDBLZUEUIUDBUDBARUKSTUAUB $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Inner product (pre-Hilbert) spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CPreHilOLD $.

  $( Extend class notation with the class of all complex inner product spaces
     (also called pre-Hilbert spaces). $)
  ccphlo $a class CPreHilOLD $.

  ${
    $d g n s x y $.
    $( Define the class of all complex inner product spaces.  An inner product
       space is a normed vector space whose norm satisfies the parallelogram
       law (a property that induces an inner product).  Based on Exercise 4(b)
       of [ReedSimon] p. 63.  The vector operation is ` g ` , the scalar
       product is ` s ` , and the norm is ` n ` .  An inner product space is
       also called a pre-Hilbert space.  (Contributed by NM, 2-Apr-2007.)
       (New usage is discouraged.) $)
    df-ph $a |- CPreHilOLD = ( NrmCVec i^i { <. <. g , s >. , n >. |
          A. x e. ran g A. y e. ran g
       ( ( ( n ` ( x g y ) ) ^ 2 ) + ( ( n ` ( x g ( -u 1 s y ) ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( n ` x ) ^ 2 ) + ( ( n ` y ) ^ 2 ) ) ) } ) $.

    $( Every complex inner product space is a normed complex vector space.
       (Contributed by NM, 2-Apr-2007.)  (New usage is discouraged.) $)
    phnv $p |- ( U e. CPreHilOLD -> U e. NrmCVec ) $=
      ( vx vy vg vn vs ccphlo cnv cv co cfv c2 cexp c1 cneg caddc cmul wceq crn
      wral coprab cin df-ph inss1 eqsstri sseli ) GHAGHBIZCIZDIZJEIZKLMJUGNOUHF
      IJUIJUJKLMJPJLUGUJKLMJUHUJKLMJPJQJRCUISZTBUKTDFEUAZUBHBCDEFUCHULUDUEUF $.

    $( The class of all complex inner product spaces is a relation.
       (Contributed by NM, 2-Apr-2007.)  (New usage is discouraged.) $)
    phrel $p |- Rel CPreHilOLD $=
      ( vx ccphlo cnv wss wrel cv phnv ssriv nvrel relss mp2 ) BCDCEBEABCAFGHIB
      CJK $.
  $}

  ${
    phnvi.1 $e |- U e. CPreHilOLD $.
    $( Every complex inner product space is a normed complex vector space.
       (Contributed by NM, 20-Nov-2007.)  (New usage is discouraged.) $)
    phnvi $p |- U e. NrmCVec $=
      ( ccphlo wcel cnv phnv ax-mp ) ACDAEDBAFG $.
  $}

  ${
    $d g n s x y G $.  $d g n s x y N $.  $d g n s x y S $.  $d g n s x y X $.
    isphg.1 $e |- X = ran G $.
    $( The predicate "is a complex inner product space."  An inner product
       space is a normed vector space whose norm satisfies the parallelogram
       law.  The vector (group) addition operation is ` G ` , the scalar
       product is ` S ` , and the norm is ` N ` .  An inner product space is
       also called a pre-Hilbert space.  (Contributed by NM, 2-Apr-2007.)
       (New usage is discouraged.) $)
    isphg $p |- ( ( G e. A /\ S e. B /\ N e. C ) ->
  ( <. <. G , S >. , N >. e. CPreHilOLD <-> ( <. <. G , S >. , N >. e. NrmCVec
        /\
          A. x e. X A. y e. X
      ( ( ( N ` ( x G y ) ) ^ 2 ) + ( ( N ` ( x G ( -u 1 S y ) ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( N ` x ) ^ 2 ) + ( ( N ` y ) ^ 2 ) ) ) ) ) ) $=
      ( wcel cv co cfv c2 cexp caddc wceq wral oveq1d vg vn cop ccphlo cnv cneg
      vs c1 cmul crn coprab wa w3a df-ph elin2 rneq eqtr4di oveq fveq2d oveq12d
      eqeq1d raleqbidv oveq2d 2ralbidv fveq1 eqeq12d eloprabg anbi2d bitrid ) G
      FUCHUCZUDKVJUEKZVJALZBLZUALZMZUBLZNZOPMZVLUHUFZVMUGLZMZVNMZVPNZOPMZQMZOVL
      VPNZOPMZVMVPNZOPMZQMZUIMZRZBVNUJZSZAWMSZUAUGUBUKZKZULGCKFDKHEKUMZVKVLVMGM
      ZHNZOPMZVLVSVMFMZGMZHNZOPMZQMZOVLHNZOPMZVMHNZOPMZQMZUIMZRZBISAISZULVJUEWP
      UDABUAUBUGUNUOWRWQXNVKWOWSVPNZOPMZVLWAGMZVPNZOPMZQMZWKRZBISZAISXPXCVPNZOP
      MZQMZWKRZBISAISXNUAUGUBGFHCDEVNGRZWNYBAWMIYGWMGUJIVNGUPJUQZYGWLYABWMIYHYG
      WEXTWKYGVRXPWDXSQYGVQXOOPYGVOWSVPVLVMVNGURUSTYGWCXROPYGWBXQVPVLWAVNGURUST
      UTVAVBVBVTFRZYAYFABIIYIXTYEWKYIXSYDXPQYIXRYCOPYIXQXCVPYIWAXBVLGVSVMVTFURV
      CUSTVCVAVDVPHRZYFXMABIIYJYEXFWKXLYJXPXAYDXEQYJXOWTOPWSVPHVETYJYCXDOPXCVPH
      VETUTYJWJXKOUIYJWGXHWIXJQYJWFXGOPVLVPHVETYJWHXIOPVMVPHVETUTVCVFVDVGVHVI
      $.
  $}

  ${
    phop.2 $e |- G = ( +v ` U ) $.
    phop.4 $e |- S = ( .sOLD ` U ) $.
    phop.6 $e |- N = ( normCV ` U ) $.
    $( A complex inner product space in terms of ordered pair components.
       (Contributed by NM, 2-Apr-2007.)  (New usage is discouraged.) $)
    phop $p |- ( U e. CPreHilOLD -> U = <. <. G , S >. , N >. ) $=
      ( ccphlo wcel c1st cfv c2nd cop wrel wceq phrel 1st2nd mpan nmcvfval cvc
      opeq2i cnv phnv eqid nvvc vcrel vafval smfval opeq12i eqtr4di 3syl opeq1d
      eqtr3id eqtrd ) BHIZBBJKZBLKZMZCAMZDMZHNUOBUROPBHQRUOURUPDMUTDUQUPBDGSUAU
      OUPUSDUOBUBIUPTIZUPUSOBUCBUPUPUDUEVAUPUPJKZUPLKZMZUSTNVAUPVDOUFUPTQRCVBAV
      CBCEUGABFUHUIUJUKULUMUN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples of pre-Hilbert spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    cncph.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The set of complex numbers is an inner product (pre-Hilbert) space.
       (Contributed by Steve Rodriguez, 28-Apr-2007.)  (Revised by Mario
       Carneiro, 7-Nov-2013.)  (New usage is discouraged.) $)
    cncph $p |- U e. CPreHilOLD $=
      ( vx vy caddc cmul cop cabs ccphlo wcel cv co c2 cexp wceq cc eqtrd recnd
      cfv cvv cnv c1 cneg wral eqid cnnv cmin mulm1 adantl oveq2d negsub fveq2d
      wa oveq1d ccj cre sqabsadd sqabssub oveq12d abscl sqcld addcl syl2an cjcl
      2cn mulcl sylan2 recl syl sylancr ppncand 2times eqcomd rgen2 addex mulex
      wb cr wf absf fex mp2an cablo cgr cnaddabloOLD ablogrpo ax-mp cxp ax-addf
      cnex fdmi grporn isphg mp3an mpbir2an eqeltri ) AEFGHGZIBWQIJZWQUAJZCKZDK
      ZELHSMNLZWTUBUCXAFLZELZHSZMNLZELZMWTHSZMNLZXAHSZMNLZELZFLZOZDPUDCPUDZWQWQ
      UEUFXNCDPPWTPJZXAPJZUMZXGXBWTXAUGLZHSZMNLZELZXMXRXFYAXBEXRXEXTMNXRXDXSHXR
      XDWTXAUCZELXSXRXCYCWTEXQXCYCOXPXAUHUIUJWTXAUKQULUNUJXRYBXLXLELZXMXRYBXLMW
      TXAUOSZFLZUPSZFLZELZXLYHUGLZELYDXRXBYIYAYJEWTXAUQWTXAURUSXRXLYHXLXPXIPJXK
      PJXLPJZXQXPXHXPXHWTUTRVAXQXJXQXJXAUTRVAXIXKVBVCZXRMPJYGPJZYHPJVEXRYFPJZYM
      XQXPYEPJYNXAVDWTYEVFVGYNYGYFVHRVIMYGVFVJYLVKQXRYKYDXMOYLYKXMYDXLVLVMVIQQV
      NETJFTJHTJZWRWSXOUMVQVOVPPVRHVSPTJYOVTWJPVRTHWAWBCDTTTFEHPEPEWCJEWDJWEEWF
      WGPPWHPEWIWKWLWMWNWOWP $.
  $}

  ${
    elimph.1 $e |- X = ( BaseSet ` U ) $.
    elimph.5 $e |- Z = ( 0vec ` U ) $.
    elimph.6 $e |- U e. CPreHilOLD $.
    $( TODO - use elimnvOLD ? $)
    $( Hypothesis elimination lemma for complex inner product spaces to assist
       weak deduction theorem.  (Contributed by NM, 27-Apr-2007.)
       (New usage is discouraged.) $)
    elimph $p |- if ( A e. X , A , Z ) e. X $=
      ( phnvi elimnv ) ABCDEFBGHI $.
  $}

  $( TODO - use elimnvu ? $)
  $( Hypothesis elimination lemma for complex inner product spaces to assist
     weak deduction theorem.  (Contributed by NM, 6-May-2007.)
     (New usage is discouraged.) $)
  elimphu $p |- if ( U e. CPreHilOLD , U , <. <. + , x. >. , abs >. )
                 e. CPreHilOLD $=
    ( caddc cmul cop cabs ccphlo eqid cncph elimel ) ABCDEDZFJJGHI $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Properties of pre-Hilbert spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y A $.  $d y B $.  $d x y G $.  $d x y M $.  $d x y N $.  $d x y U $.
    $d x y X $.
    isph.1 $e |- X = ( BaseSet ` U ) $.
    isph.2 $e |- G = ( +v ` U ) $.
    isph.3 $e |- M = ( -v ` U ) $.
    isph.6 $e |- N = ( normCV ` U ) $.
    $( The predicate "is an inner product space."  (Contributed by NM,
       1-Feb-2008.)  (New usage is discouraged.) $)
    isph $p |- ( U e. CPreHilOLD <-> ( U e. NrmCVec /\ A. x e. X A. y e. X
      ( ( ( N ` ( x G y ) ) ^ 2 ) + ( ( N ` ( x M y ) ) ^ 2 ) ) = (
      2 x. ( ( ( N ` x ) ^ 2 ) + ( ( N ` y ) ^ 2 ) ) ) ) ) $=
      ( wcel co cfv c2 cexp caddc wceq wa cvv ccphlo cnv cmul wral phnv cns cop
      cv wb eqid nvop eleq1 cneg cpv fvexi fvex cnmcv bafval isphg mp3an nvmval
      c1 3expa fveq2d oveq1d oveq2d eqeq1d ralbidva pm5.32i anbi1d bitrid bitrd
      bitr2id syl bianabs biadanii ) CUALZCUBLZAUHZBUHZDMFNOPMZVSVTEMZFNZOPMZQM
      ZOVSFNOPMVTFNOPMQMUCMZRZBGUDZAGUDZCUEVRVQWIVRCDCUFNZUGFUGZRZVQVRWISZUIWJC
      DFIWJUJZKUKWLVQWKUALZWMCWKUAULWOWKUBLZWAVSVBUMVTWJMDMZFNZOPMZQMZWFRZBGUDZ
      AGUDZSZWLWMDTLWJTLFTLWOXDUIDCUNIUOCUFUPFCUQKUOABTTTWJDFGCDGHIURUSUTWMVRXC
      SWLXDVRWIXCVRWHXBAGVRVSGLZSZWGXABGXFVTGLZSZWEWTWFXHWDWSWAQXHWCWROPXHWBWQF
      VRXEXGWBWQRVSVTWJCDEGHIWNJVAVCVDVEVFVGVHVHVIWLVRWPXCCWKUBULVJVMVKVLVNVOVP
      $.

    $( The parallelogram law for an inner product space.  (Contributed by NM,
       2-Apr-2007.)  (New usage is discouraged.) $)
    phpar2 $p |- ( ( U e. CPreHilOLD /\ A e. X /\ B e. X ) ->
      ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A M B ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) ) $=
      ( vx co cfv c2 cexp caddc cmul wceq oveq1d vy ccphlo wcel w3a cv wral cnv
      isph simprbi 3ad2ant1 wi fvoveq1 oveq12d fveq2 oveq2d oveq2 fveq2d rspc2v
      eqeq12d 3adant1 mpd ) CUBUCZAGUCZBGUCZUDLUEZUAUEZDMFNZOPMZVEVFEMFNZOPMZQM
      ZOVEFNZOPMZVFFNZOPMZQMZRMZSZUAGUFLGUFZABDMZFNZOPMZABEMZFNZOPMZQMZOAFNZOPM
      ZBFNZOPMZQMZRMZSZVBVCVSVDVBCUGUCVSLUACDEFGHIJKUHUIUJVCVDVSWMUKVBVRWMAVFDM
      ZFNZOPMZAVFEMZFNZOPMZQMZOWHVOQMZRMZSLUAABGGVEASZVKWTVQXBXCVHWPVJWSQXCVGWO
      OPVEAVFFDULTXCVIWROPVEAVFFEULTUMXCVPXAORXCVMWHVOQXCVLWGOPVEAFUNTTUOUSVFBS
      ZWTWFXBWLXDWPWBWSWEQXDWOWAOPXDWNVTFVFBADUPUQTXDWRWDOPXDWQWCFVFBAEUPUQTUMX
      DXAWKORXDVOWJWHQXDVNWIOPVFBFUNTUOUOUSURUTVA $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y G $.  $d x y N $.  $d x y S $.  $d x y X $.
    phpar.1 $e |- X = ( BaseSet ` U ) $.
    phpar.2 $e |- G = ( +v ` U ) $.
    phpar.4 $e |- S = ( .sOLD ` U ) $.
    phpar.6 $e |- N = ( normCV ` U ) $.
    $( The parallelogram law for an inner product space.  (Contributed by NM,
       2-Apr-2007.)  (New usage is discouraged.) $)
    phpar $p |- ( ( U e. CPreHilOLD /\ A e. X /\ B e. X ) ->
      ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A G ( -u 1 S B ) ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) ) $=
      ( wcel co cfv c2 cexp caddc cmul cvv oveq1d vx vy ccphlo w3a cv cneg wceq
      c1 wral cop cpv fvexi cns cnmcv 3pm3.2i phop eleq1d bafval isphg simplbda
      ibi sylancr 3ad2ant1 wi fvoveq1 oveq12d fveq2 oveq2d eqeq12d oveq2 fveq2d
      cnv rspc2v 3adant1 mpd ) DUCLZAGLZBGLZUDUAUEZUBUEZEMFNZOPMZVSUHUFZVTCMZEM
      FNZOPMZQMZOVSFNZOPMZVTFNZOPMZQMZRMZUGZUBGUIUAGUIZABEMZFNZOPMZAWCBCMZEMZFN
      ZOPMZQMZOAFNZOPMZBFNZOPMZQMZRMZUGZVPVQWOVRVPESLZCSLZFSLZUDZECUJFUJZUCLZWO
      XKXLXMEDUKIULCDUMJULFDUNKULUOVPXPVPDXOUCCDEFIJKUPUQVAXNXPXOVLLWOUAUBSSSCE
      FGDEGHIURUSUTVBVCVQVRWOXJVDVPWNXJAVTEMZFNZOPMZAWDEMZFNZOPMZQMZOXEWKQMZRMZ
      UGUAUBABGGVSAUGZWGYCWMYEYFWBXSWFYBQYFWAXROPVSAVTFEVETYFWEYAOPVSAWDFEVETVF
      YFWLYDORYFWIXEWKQYFWHXDOPVSAFVGTTVHVIVTBUGZYCXCYEXIYGXSWRYBXBQYGXRWQOPYGX
      QWPFVTBAEVJVKTYGYAXAOPYGXTWTFYGWDWSAEVTBWCCVJVHVKTVFYGYDXHORYGWKXGXEQYGWJ
      XFOPVTBFVGTVHVHVIVMVNVO $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y G $.  $d x y N $.  $d x y S $.  $d x y X $.
    ip1i.1 $e |- X = ( BaseSet ` U ) $.
    ip1i.2 $e |- G = ( +v ` U ) $.
    ip1i.4 $e |- S = ( .sOLD ` U ) $.
    ip1i.7 $e |- P = ( .iOLD ` U ) $.
    ip1i.9 $e |- U e. CPreHilOLD $.
    ${
      ip1i.a $e |- A e. X $.
      ip1i.b $e |- B e. X $.
      ip1i.c $e |- C e. X $.
      ${
        ip1i.6 $e |- N = ( normCV ` U ) $.
        ip0i.j $e |- J e. CC $.
        $( A slight variant of Equation 6.46 of [Ponnusamy] p. 362, where ` J `
           is either 1 or -1 to represent +-1.  (Contributed by NM,
           23-Apr-2007.)  (New usage is discouraged.) $)
        ip0i $p |- ( ( ( ( N ` ( ( A G B ) G ( J S C ) ) ) ^ 2 ) -
             ( ( N ` ( ( A G B ) G ( -u J S C ) ) ) ^ 2 ) ) +
             ( ( ( N ` ( ( A G ( -u 1 S B ) ) G ( J S C ) ) ) ^ 2 ) -
           ( ( N ` ( ( A G ( -u 1 S B ) ) G ( -u J S C ) ) ) ^ 2 ) ) ) =
                ( 2 x. ( ( ( N ` ( A G ( J S C ) ) ) ^ 2 ) -
                ( ( N ` ( A G ( -u J S C ) ) ) ^ 2 ) ) ) $=
          ( c2 co cfv cexp cneg cmin cmul caddc c1 2cn phnvi cnv cc nvscl mp3an
          wcel nvgcl nvcli recni sqcli negcli subdii wceq mulcli pnpcan2 eqtr4i
          cablo w3a c1st cvc eqid nvvc vafval vcablo mp2b 3pm3.2i bafval ablo32
          fveq2i oveq1i neg1cn oveq12i ccphlo adddii 3eqtri addsub4i 3eqtr2ri
          mp2an phpar ) UAAHCEUBZGUBZIUCZUAUDUBZAHUEZCEUBZGUBZIUCZUAUDUBZUFUBUG
          UBZUAWMUGUBZUABIUCZUAUDUBZUGUBZUHUBZUAWRUGUBZXCUHUBZUFUBZABGUBZWJGUBZ
          IUCZUAUDUBZAUIUEZBEUBZGUBZWJGUBZIUCZUAUDUBZUHUBZXHWOGUBZIUCZUAUDUBZXN
          WOGUBZIUCZUAUDUBZUHUBZUFUBXKYAUFUBXQYDUFUBUHUBWSWTXEUFUBZXGUAWMWRUJWL
          WLWKFIJKSFOUKZFULUPZAJUPZWJJUPZWKJUPZYGPYHHUMUPCJUPZYJYGTRHCEFJKMUNUO
          ZAWJFGJKLUQUOZURUSUTZWQWQWPFIJKSYGYHYIWOJUPZWPJUPZYGPYHWNUMUPYLYPYGHT
          VARWNCEFJKMUNUOZAWOFGJKLUQUOZURUSUTZVBWTUMUPXEUMUPXCUMUPXGYFVCUAWMUJY
          OVDUAWRUJYTVDUAXBUJXAXABFIJKSYGQURUSUTZVDWTXEXCVEUOVFXRXDYEXFUFXRWKBG
          UBZIUCZUAUDUBZWKXMGUBZIUCZUAUDUBZUHUBZUAWMXBUHUBUGUBZXDXKUUDXQUUGUHXJ
          UUCUAUDXIUUBIGVGUPZYIBJUPZYJVHXIUUBVCYHFVIUCZVJUPUUJYGFUULUULVKVLGUUL
          FGLVMVNVOZYIUUKYJPQYMVPABWJGJFGJKLVQZVRWHVSVTXPUUFUAUDXOUUEIUUJYIXMJU
          PZYJVHXOUUEVCUUMYIUUOYJPYHXLUMUPUUKUUOYGWAQXLBEFJKMUNUOZYMVPAXMWJGJUU
          NVRWHVSVTWBFWCUPZYKUUKUUHUUIVCOYNQWKBEFGIJKLMSWIUOUAWMXBUJYOUUAWDWEYE
          WPBGUBZIUCZUAUDUBZWPXMGUBZIUCZUAUDUBZUHUBZUAWRXBUHUBUGUBZXFYAUUTYDUVC
          UHXTUUSUAUDXSUURIUUJYIUUKYPVHXSUURVCUUMYIUUKYPPQYRVPABWOGJUUNVRWHVSVT
          YCUVBUAUDYBUVAIUUJYIUUOYPVHYBUVAVCUUMYIUUOYPPUUPYRVPAXMWOGJUUNVRWHVSV
          TWBUUQYQUUKUVDUVEVCOYSQWPBEFGIJKLMSWIUOUAWRXBUJYTUUAWDWEWBXKXQYAYDXJX
          JXIFIJKSYGYHXHJUPZYJXIJUPYGYHYIUUKUVFYGPQABFGJKLUQUOZYMXHWJFGJKLUQUOU
          RUSUTXPXPXOFIJKSYGYHXNJUPZYJXOJUPYGYHYIUUOUVHYGPUUPAXMFGJKLUQUOZYMXNW
          JFGJKLUQUOURUSUTXTXTXSFIJKSYGYHUVFYPXSJUPYGUVGYRXHWOFGJKLUQUOURUSUTYC
          YCYBFIJKSYGYHUVHYPYBJUPYGUVIYRXNWOFGJKLUQUOURUSUTWFWG $.

        $( Lemma for ~ ip1i .  (Contributed by NM, 21-Apr-2007.)
           (New usage is discouraged.) $)
        ip1ilem $p |- ( ( ( A G B ) P C ) +
                         ( ( A G ( -u 1 S B ) ) P C ) ) = ( 2 x. ( A P C ) ) $=
          ( c4 co c1 cneg caddc cmul cdiv c2 cfv cexp cmin ci wcel wceq 4ipval2
          cnv phnvi mp3an oveq2i 2cn 4cn dipcl mul12i nvgcl nvcli resqcli recni
          cc ax-1cn negcli nvscl subcli ax-icn mulcli adddii nvsid mp2an fveq2i
          ip0i oveq1i oveq12i 3eqtr3i eqtr4i eqtr2i 3eqtri 3eqtr3ri addcli 4ne0
          add4i divcan3i ) UAABGUBZCDUBZAUCUDZBEUBZGUBZCDUBZUEUBZUFUBZUAUGUBUAU
          HACDUBZUFUBZUFUBZUAUGUBWQWTWRXAUAUGUHUAWSUFUBZUFUBUHACGUBZIUIZUHUJUBZ
          AWMCEUBZGUBZIUIZUHUJUBZUKUBZULAULCEUBZGUBZIUIZUHUJUBZAULUDZCEUBZGUBZI
          UIZUHUJUBZUKUBZUFUBZUEUBZUFUBZXAWRXBYBUHUFFUPUMZAJUMZCJUMZXBYBUNFOUQZ
          PRACDEFGIJKLMSNUOURUSUHUAWSUTVAYDYEYFWSVHUMYGPRACDFJKNVBURZVCYCWKCGUB
          ZIUIZUHUJUBZWKXFGUBZIUIZUHUJUBZUKUBZWOCGUBZIUIZUHUJUBZWOXFGUBZIUIZUHU
          JUBZUKUBZUEUBZULWKXKGUBZIUIZUHUJUBZWKXPGUBZIUIZUHUJUBZUKUBZUFUBZULWOX
          KGUBZIUIZUHUJUBZWOXPGUBZIUIZUHUJUBZUKUBZUFUBZUEUBZUEUBZYOUUKUEUBZUUBU
          USUEUBZUEUBZWRYCUHXJUFUBZUHYAUFUBZUEUBUVAUHXJYAUTXEXIXEXDXCFIJKSYGYDY
          EYFXCJUMYGPRACFGJKLVDURVEVFVGXIXHXGFIJKSYGYDYEXFJUMZXGJUMYGPYDWMVHUMZ
          YFUVGYGUCVIVJZRWMCEFJKMVKURZAXFFGJKLVDURVEVFVGVLULXTVMXNXSXNXMXLFIJKS
          YGYDYEXKJUMZXLJUMYGPYDULVHUMYFUVKYGVMRULCEFJKMVKURZAXKFGJKLVDURVEVFVG
          XSXRXQFIJKSYGYDYEXPJUMZXQJUMYGPYDXOVHUMYFUVMYGULVMVJRXOCEFJKMVKURZAXP
          FGJKLVDURVEVFVGVLZVNVOUUCUVEUUTUVFUEWKUCCEUBZGUBZIUIZUHUJUBZYNUKUBZWO
          UVPGUBZIUIZUHUJUBZUUAUKUBZUEUBUHAUVPGUBZIUIZUHUJUBZXIUKUBZUFUBUUCUVEA
          BCDEFGUCIJKLMNOPQRSVIVSUVTYOUWDUUBUEUVSYKYNUKUVRYJUHUJUVQYIIUVPCWKGYD
          YFUVPCUNYGRCEFJKMVPVQZUSVRVTVTUWCYRUUAUKUWBYQUHUJUWAYPIUVPCWOGUWIUSVR
          VTVTWAUWHXJUHUFUWGXEXIUKUWFXDUHUJUWEXCIUVPCAGUWIUSVRVTVTUSWBULUUJUURU
          EUBZUFUBULUHXTUFUBZUFUBUUTUVFUWJUWKULUFABCDEFGULIJKLMNOPQRSVMVSUSULUU
          JUURVMUUFUUIUUFUUEUUDFIJKSYGYDWKJUMZUVKUUDJUMYGYDYEBJUMZUWLYGPQABFGJK
          LVDURZUVLWKXKFGJKLVDURVEVFVGUUIUUHUUGFIJKSYGYDUWLUVMUUGJUMYGUWNUVNWKX
          PFGJKLVDURVEVFVGVLZUUNUUQUUNUUMUULFIJKSYGYDWOJUMZUVKUULJUMYGYDYEWNJUM
          ZUWPYGPYDUVHUWMUWQYGUVIQWMBEFJKMVKURAWNFGJKLVDURZUVLWOXKFGJKLVDURVEVF
          VGUUQUUPUUOFIJKSYGYDUWPUVMUUOJUMYGUWRUVNWOXPFGJKLVDURVEVFVGVLZVOULUHX
          TVMUTUVOVCWBWAWCYOUUBUUKUUSYKYNYKYJYIFIJKSYGYDUWLYFYIJUMYGUWNRWKCFGJK
          LVDURVEVFVGYNYMYLFIJKSYGYDUWLUVGYLJUMYGUWNUVJWKXFFGJKLVDURVEVFVGVLYRU
          UAYRYQYPFIJKSYGYDUWPYFYPJUMYGUWRRWOCFGJKLVDURVEVFVGUUAYTYSFIJKSYGYDUW
          PUVGYSJUMYGUWRUVJWOXFFGJKLVDURVEVFVGVLULUUJVMUWOVNULUURVMUWSVNWIWRUAW
          LUFUBZUAWPUFUBZUEUBUVDUAWLWPVAYDUWLYFWLVHUMYGUWNRWKCDFJKNVBURZYDUWPYF
          WPVHUMYGUWRRWOCDFJKNVBURZVOUWTUVBUXAUVCUEYDUWLYFUWTUVBUNYGUWNRWKCDEFG
          IJKLMSNUOURYDUWPYFUXAUVCUNYGUWRRWOCDEFGIJKLMSNUOURWAWDWEWFVTWQUAWLWPU
          XBUXCWGVAWHWJWTUAUHWSUTYHVNVAWHWJWB $.
      $}

      $( Equation 6.47 of [Ponnusamy] p. 362.  (Contributed by NM,
         27-Apr-2007.)  (New usage is discouraged.) $)
      ip1i $p |- ( ( ( A G B ) P C ) +
                       ( ( A G ( -u 1 S B ) ) P C ) ) = ( 2 x. ( A P C ) ) $=
        ( c1 cnmcv cfv eqid ax-1cn ip1ilem ) ABCDEFGQFRSZHIJKLMNOPUCTUAUB $.
    $}

    ${
      ip2i.8 $e |- A e. X $.
      ip2i.9 $e |- B e. X $.
      $( Equation 6.48 of [Ponnusamy] p. 362.  (Contributed by NM,
         26-Apr-2007.)  (New usage is discouraged.) $)
      ip2i $p |- ( ( 2 S A ) P B ) = ( 2 x. ( A P B ) ) $=
        ( co c1 caddc cc0 wcel wceq c2 cneg cmul cnv cc phnvi nvgcl mp3an dipcl
        addridi cn0v cfv eqid nvrinv mp2an oveq1i dip0l eqtri oveq2i w3a ax-1cn
        df-2 3pm3.2i nvdir nvsid oveq12i 3eqtr4ri ip1i ) UAADOZBCOZAAFOZBCOZAPU
        BADOFOZBCOZQOZUAABCOUCOVLRQOVLVOVJVLEUDSZVKGSZBGSZVLUESELUFZVPAGSZVTVQV
        SMMAAEFGHIUGUHNVKBCEGHKUIUHUJVNRVLQVNEUKULZBCOZRVMWABCVPVTVMWATVSMADEFG
        WAHIJWAUMZUNUOUPVPVRWBRTVSNBCEGWAHWCKUQUOURUSVIVKBCVIPPQOZADOZVKUAWDADV
        BUPWEPADOZWFFOZVKVPPUESZWHVTUTWEWGTVSWHWHVTVAVAMVCPPADEFGHIJVDUOWFAWFAF
        VPVTWFATVSMADEGHJVEUOZWIVFURURUPVGAABCDEFGHIJKLMMNVHUR $.
    $}

    ${
      ipdiri.8 $e |- A e. X $.
      ipdiri.9 $e |- B e. X $.
      ipdiri.10 $e |- C e. X $.
      $( Lemma for ~ ipdiri .  (Contributed by NM, 26-Apr-2007.)
         (New usage is discouraged.) $)
      ipdirilem $p |- ( ( A G B ) P C ) = ( ( A P C ) + ( B P C ) ) $=
        ( co wcel wceq mp2an c2 c1 cdiv cmul cneg caddc 2thalfe1 oveq1i cnv w3a
        cc phnvi 2cn halfcn nvgcl mp3an 3pm3.2i nvsass nvsid 3eqtr3i nvscl ip2i
        eqtr3i neg1cn ip1i cn0v cfv cablo wa c1st eqid nvvc ax-mp vafval vcablo
        cvc pm3.2i bafval ablo4 smfval vc2OLD nvrinv oveq12i nv0rid 3eqtri nvdi
        oveq2i eqtr4i ax-1cn 2ne0 divcan1i mulcomi neg1mulneg1e1 nv0lid 3eqtr2i
        eqtri ) ABGQZCDQZUAUBUAUCQZWQEQZCDQUDQZWTWSAUBUEZBEQZGQZEQZGQZCDQZWTXBX
        EEQZGQZCDQZUFQACDQZBCDQZUFQUAWTEQZCDQWRXAXMWQCDUAWSUDQZWQEQZUBWQEQZXMWQ
        XNUBWQEUGUHFUIRZUAUKRZWSUKRZWQHRZUJXOXMSFMULZXRXSXTUMUNXQAHRZBHRZXTYANO
        ABFGHIJUOUPZUQUAWSWQEFHIKURTXQXTXPWQSYAYDWQEFHIKUSTUTUHWTCDEFGHIJKLMXQX
        SXTWTHRYAUNYDWSWQEFHIKVAUPZPVBVCWTXECDEFGHIJKLMYEXQXSXDHRZXEHRYAUNXQYBX
        CHRZYFYANXQXBUKRZYCYGYAVDOXBBEFHIKVAUPZAXCFGHIJUOUPZWSXDEFHIKVAUPPVEXGX
        KXJXLUFXFACDWSWQXDGQZEQZWSUAUDQZAEQZXFAYLWSUAAEQZEQZYNYKYOWSEYKAAGQZBXC
        GQZGQZYOFVFVGZGQZYOGVHRZYBYCVIZYBYGVIYKYSSFVJVGZVPRZUUBXQUUEYAFUUDUUDVK
        VLVMZGUUDFGJVNZVOVMZYBYCNOVQZYBYGNYIVQABAXCGHFGHIJVRZVSUPYQYOYRYTGUUEYB
        YQYOSUUFNAEGUUDHUUGEFKVTZUUJWATXQYCYRYTSYAOBEFGHYTIJKYTVKZWBTWCXQYOHRZU
        UAYOSYAXQXRYBUUMYAUMNUAAEFHIKVAUPYOFGHYTIJUULWDTWEWGXQXSXRYBUJYNYPSYAXS
        XRYBUNUMNUQWSUAAEFHIKURTWHXQXSXTYFUJYLXFSYAXSXTYFUNYDYJUQWSWQXDEFGHIJKW
        FTYNUBAEQZAYMUBAEUBUAWIUMWJWKZUHXQYBUUNASYANAEFHIKUSTWPUTUHXIBCDXIWSWQX
        BAEQZBGQZGQZEQZUBBEQZBXIWTWSUUQEQZGQZUUSXHUVAWTGXBWSUDQZXDEQZWSXBUDQZXD
        EQZXHUVAUVCUVEXDEXBWSVDUNWLUHXQYHXSYFUJUVDXHSYAYHXSYFVDUNYJUQXBWSXDEFHI
        KURTUVFWSXBXDEQZEQZUVAXQXSYHYFUJUVFUVHSYAXSYHYFUNVDYJUQWSXBXDEFHIKURTUV
        GUUQWSEUVGUUPXBXCEQZGQZUUQXQYHYBYGUJUVGUVJSYAYHYBYGVDNYIUQXBAXCEFGHIJKW
        FTUVIBUUPGXBXBUDQZBEQZUUTUVIBUVKUBBEWMUHXQYHYHYCUJUVLUVISYAYHYHYCVDVDOU
        QXBXBBEFHIKURTXQYCUUTBSYAOBEFHIKUSTZUTWGWPWGWPUTWGXQXSXTUUQHRZUJUUSUVBS
        YAXSXTUVNUNYDXQUUPHRZYCUVNYAXQYHYBUVOYAVDNXBAEFHIKVAUPZOUUPBFGHIJUOUPUQ
        WSWQUUQEFGHIJKWFTWHUUSWSUABEQZEQZYMBEQZUUTUURUVQWSEUURAUUPGQZBBGQZGQZUW
        AUVQUUBUUCUVOYCVIUURUWBSUUHUUIUVOYCUVPOVQABUUPBGHUUJVSUPUWBYTUWAGQZUWAU
        VTYTUWAGXQYBUVTYTSYANAEFGHYTIJKUULWBTUHXQUWAHRZUWCUWASYAXQYCYCUWDYAOOBB
        FGHIJUOUPUWAFGHYTIJUULWNTWPUUEYCUWAUVQSUUFOBEGUUDHUUGUUKUUJWATWEWGXQXSX
        RYCUJUVSUVRSYAXSXRYCUNUMOUQWSUABEFHIKURTYMUBBEUUOUHWOUVMWEUHWCWO $.
    $}

    $( Distributive law for inner product.  Equation I3 of [Ponnusamy] p. 362.
       (Contributed by NM, 27-Apr-2007.)  (New usage is discouraged.) $)
    ipdiri $p |- ( ( A e. X /\ B e. X /\ C e. X ) ->
                 ( ( A G B ) P C ) = ( ( A P C ) + ( B P C ) ) ) $=
      ( wcel co caddc wceq cif oveq1 oveq2 cn0v cfv oveq1d eqeq12d oveq12d eqid
      oveq2d elimph ipdirilem dedth3h ) AHNZBHNZCHNZABGOZCDOZACDOZBCDOZPOZQUKAF
      UAUBZRZBGOZCDOZUTCDOZUQPOZQUTULBUSRZGOZCDOZVCVECDOZPOZQVFUMCUSRZDOZUTVJDO
      ZVEVJDOZPOZQABCUSUSUSAUTQZUOVBURVDVOUNVACDAUTBGSUCVOUPVCUQPAUTCDSUCUDBVEQ
      ZVBVGVDVIVPVAVFCDBVEUTGTUCVPUQVHVCPBVECDSUGUDCVJQZVGVKVIVNCVJVFDTVQVCVLVH
      VMPCVJUTDTCVJVEDTUEUDUTVEVJDEFGHIJKLMAFHUSIUSUFZMUHBFHUSIVRMUHCFHUSIVRMUH
      UIUJ $.

    ${
      $d j k A $.  $d j k B $.  $d j k C $.  $d j N $.  $d j k P $.
      $d j k S $.  $d j k X $.
      ipasslem1.b $e |- B e. X $.
      $( Lemma for ~ ipassi .  Show the inner product associative law for
         nonnegative integers.  (Contributed by NM, 27-Apr-2007.)
         (New usage is discouraged.) $)
      ipasslem1 $p |- ( ( N e. NN0 /\ A e. X ) ->
                      ( ( N S A ) P B ) = ( N x. ( A P B ) ) ) $=
        ( wcel co cmul wceq cc0 oveq1 vj vk cn0 cv wi c1 caddc wa cc ax-1cn cnv
        nn0cn w3a phnvi nvdir mpan mp3an2 sylan nvsid adantl oveq2d eqtrd dipcl
        oveq1d mp3an13 nvscl mp3an1 ipdiri mp3an3 sylancom eqtr4d adddir syl2an
        mullidd sylan9eq adantr exp31 a2d cn0v cfv eqid dip0l mp2an nv0 3eqtr4a
        mul02d eqeq12d imbi2d nn0indALT imp ) GUCOAHOZGADPZBCPZGABCPZQPZRZWKUAU
        DZADPZBCPZWQWNQPZRZUEWKSADPZBCPZSWNQPZRZUEWKUBUDZADPZBCPZXFWNQPZRZUEWKX
        FUFUGPZADPZBCPZXKWNQPZRZUEWKWPUEUAUBGXFUCOZWKXJXOXPWKXJXOXPWKUHZXJUHXMX
        IUFWNQPZUGPZXNXQXJXMXHXRUGPZXSXQXMXGAFPZBCPZXTXQXLYABCXQXLXGUFADPZFPZYA
        XPXFUIOZWKXLYDRZXFULZYEUFUIOZWKYFUJEUKOZYEYHWKUMYFEMUNZXFUFADEFHIJKUOUP
        UQURXQYCAXGFWKYCARZXPYIWKYKYJADEHIKUSUPUTVAVBVDXQXTXHWNUGPZYBXQXRWNXHUG
        WKXRWNRXPWKWNYIWKBHOZWNUIOZYJNABCEHILVCVEZVNUTVAXPWKXGHOZYBYLRZXPYEWKYP
        YGYIYEWKYPYJXFADEHIKVFVGURYPWKYMYQNXGABCDEFHIJKLMVHVIVJVKVKXHXIXRUGTVOX
        QXNXSRZXJXPYEYNYRWKYGYOYEYHYNYRUJXFUFWNVLUQVMVPVKVQVRWKEVSVTZBCPZSXCXDY
        IYMYTSRYJNBCEHYSIYSWAZLWBWCWKXBYSBCYIWKXBYSRYJADEHYSIKUUAWDUPVDWKWNYOWF
        WEWQSRZXAXEWKUUBWSXCWTXDUUBWRXBBCWQSADTVDWQSWNQTWGWHWQXFRZXAXJWKUUCWSXH
        WTXIUUCWRXGBCWQXFADTVDWQXFWNQTWGWHWQXKRZXAXOWKUUDWSXMWTXNUUDWRXLBCWQXKA
        DTVDWQXKWNQTWGWHWQGRZXAWPWKUUEWSWMWTWOUUEWRWLBCWQGADTVDWQGWNQTWGWHWIWJ
        $.

      $( Lemma for ~ ipassi .  Show the inner product associative law for
         nonpositive integers.  (Contributed by NM, 27-Apr-2007.)
         (New usage is discouraged.) $)
      ipasslem2 $p |- ( ( N e. NN0 /\ A e. X ) ->
              ( ( -u N S A ) P B ) = ( -u N x. ( A P B ) ) ) $=
        ( wcel co cmul cc cc0 wceq cn0 wa cneg nn0cn negcld phnvi dipcl mp3an13
        cnv mulcl syl2an nvscl mp3an1 sylan syl cmin caddc ax-1cn mulneg2 mpan2
        c1 mulrid negeqd eqtr2d adantr oveq1d neg1cn nvsass mpan mp3an2 mp3an12
        w3a ipasslem1 sylan2 oveq2d negsubd mulneg1 adantl adddid ipdiri mp3an3
        eqtrd mpdan cn0v eqid nvrinv dip0l mp2an eqtrdi eqtr3d mul01d sylan9eqr
        cfv 3eqtr2d subeq0d eqcomd ) GUAOZAHOZUBZGUCZABCPZQPZWTADPZBCPZWSXBXDWQ
        WTROZXAROZXBROWRWQGGUDZUEZEUIOZWRBHOZXFEMUFZNABCEHILUGUHZWTXAUJUKZWSXCH
        OZXDROZWQXEWRXNXHXIXEWRXNXKWTADEHIKULUMUNXIXNXJXOXKNXCBCEHILUGUHUOWSXBX
        DUPPXBGVAUCZADPZBCPZQPZUPPXBXSUCZUQPZSWSXDXSXBUPWSXDGXQDPZBCPZXSWSXCYBB
        CWQGROZWRXCYBTXGYDWRUBZXCGXPQPZADPZYBYEWTYFADYDWTYFTWRYDYFGVAQPZUCZWTYD
        VAROYFYITURGVAUSUTYDYHGGVBVCVDVEVFYDXPROZWRYGYBTZVGXIYDYJWRVLYKXKGXPADE
        HIKVHVIVJWBUNVFWRWQXQHOZYCXSTXIYJWRYLXKVGXPADEHIKULVKZXQBCDEFGHIJKLMNVM
        VNWBVOWSXBXSXMWQYDXRROZXSROWRXGWRYLYNYMXIYLXJYNXKNXQBCEHILUGUHUOZGXRUJU
        KVPWSXBWTXRQPZUQPZYASWSYPXTXBUQWQYDYNYPXTTWRXGYOGXRVQUKVOWSWTXAXRUQPZQP
        ZYQSWSWTXAXRWQXEWRXHVEWRXFWQXLVRWRYNWQYOVRVSWRWQYSWTSQPSWRYRSWTQWRAXQFP
        ZBCPZYRSWRYLUUAYRTZYMWRYLXJUUBNAXQBCDEFHIJKLMVTWAWCWRUUAEWDWMZBCPZSWRYT
        UUCBCXIWRYTUUCTXKADEFHUUCIJKUUCWEZWFVIVFXIXJUUDSTXKNBCEHUUCIUUELWGWHWIW
        JVOWQWTXHWKWLWJWJWNWOWP $.

      $( Lemma for ~ ipassi .  Show the inner product associative law for all
         integers.  (Contributed by NM, 27-Apr-2007.)
         (New usage is discouraged.) $)
      ipasslem3 $p |- ( ( N e. ZZ /\ A e. X ) ->
              ( ( N S A ) P B ) = ( N x. ( A P B ) ) ) $=
        ( wcel cn0 co cmul wceq oveq1d cz cr cn wa elznn0nn ipasslem1 ipasslem2
        cneg wo nnnn0 sylan adantll recn negnegd ad2antrr 3eqtr3d jaoian sylanb
        ) GUAOGPOZGUBOZGUHZUCOZUDZUIAHOZGADQZBCQZGABCQZRQZSZGUEUSVDVIVCABCDEFGH
        IJKLMNUFVCVDUDVAUHZADQZBCQZVJVGRQZVFVHVBVDVLVMSZUTVBVAPOVDVNVAUJABCDEFV
        AHIJKLMNUGUKULUTVLVFSVBVDUTVKVEBCUTVJGADUTGGUMUNZTTUOUTVMVHSVBVDUTVJGVG
        RVOTUOUPUQUR $.

      $( Lemma for ~ ipassi .  Show the inner product associative law for
         positive integer reciprocals.  (Contributed by NM, 27-Apr-2007.)
         (New usage is discouraged.) $)
      ipasslem4 $p |- ( ( N e. NN /\ A e. X ) ->
                  ( ( ( 1 / N ) S A ) P B ) = ( ( 1 / N ) x. ( A P B ) ) ) $=
        ( wcel c1 co cmul cc adantr cn wa cdiv nnrecre recnd phnvi nvscl mp3an1
        cnv sylan dipcl mp3an13 syl mulcl syl2an nncn cc0 recidd oveq1d mullidd
        wne nnne0 sylan9eq wceq nvsid simpr w3a nvsass syl3anc eqtr3d cn0 nnnn0
        mpan ipasslem1 syl2anc 3eqtrd adantl mulassd mulcanad ) GUAOZAHOZUBZPGU
        CQZADQZBCQZWCABCQZRQZGWBWDHOZWESOZVTWCSOZWAWHVTWCGUDUEZEUIOZWJWAWHEMUFZ
        WCADEHIKUGUHUJZWLWHBHOZWIWMNWDBCEHILUKULUMVTWJWFSOZWGSOWAWKWLWAWOWPWMNA
        BCEHILUKULZWCWFUNUOVTGSOZWAGUPZTZVTGUQVAWAGVBZTWBGWCRQZWFRQZGWERQZGWGRQ
        WBXCWFGWDDQZBCQZXDVTWAXCPWFRQWFVTXBPWFRVTGWSXAURZUSWAWFWQUTVCWBAXEBCWBX
        BADQZAXEVTWAXHPADQZAVTXBPADXGUSWLWAXIAVDWMADEHIKVEVMVCWBWRWJWAXHXEVDZWT
        VTWJWAWKTZVTWAVFWLWRWJWAVGXJWMGWCADEHIKVHVMVIVJUSWBGVKOZWHXFXDVDVTXLWAG
        VLTWNWDBCDEFGHIJKLMNVNVOVPWBGWCWFWTXKWAWPVTWQVQVRVJVS $.

      $( Lemma for ~ ipassi .  Show the inner product associative law for
         rational numbers.  (Contributed by NM, 27-Apr-2007.)
         (New usage is discouraged.) $)
      ipasslem5 $p |- ( ( C e. QQ /\ A e. X ) ->
                  ( ( C S A ) P B ) = ( C x. ( A P B ) ) ) $=
        ( vj vk wcel co cmul wceq cq cv cdiv cn wrex cz wi elq wa w3a c1 cc zcn
        nnrecre recnd cnv phnvi dipcl mp3an13 mulass syl3an adantr nncn cc0 wne
        adantl nnne0 divrecd 3adant3 oveq1d nvsass eqtrd nvscl mp3an1 ipasslem3
        mpan sylan sylan2 3impb ipasslem4 3adant1 oveq2d 3eqtr4rd oveq1 eqeq12d
        id 3eqtrd syl5ibrcom 3expia com23 rexlimivv sylbi imp ) CUAQZAHQZCAERZB
        DRZCABDRZSRZTZWNCOUBZPUBZUCRZTZPUDUEOUFUEWOWTUGZOPCUHXDXEOPUFUDXAUFQZXB
        UDQZUIZWOXDWTXFXGWOXDWTUGXFXGWOUJZWTXDXCAERZBDRZXCWRSRZTXIXAUKXBUCRZSRZ
        WRSRZXAXMWRSRZSRZXLXKXFXAULQZXGXMULQZWOWRULQZXOXQTXAUMZXGXMXBUNUOZFUPQZ
        WOBHQXTFMUQZNABDFHILURUSXAXMWRUTVAXIXCXNWRSXFXGXCXNTWOXHXAXBXFXRXGYAVBX
        GXBULQXFXBVCVFXGXBVDVEXFXBVGVFVHVIZVJXIXKXAXMAERZERZBDRZXAYFBDRZSRZXQXI
        XJYGBDXIXJXNAERZYGXIXCXNAEYEVJXFXRXGXSWOWOYKYGTZYAYBWOWFYCXRXSWOUJYLYDX
        AXMAEFHIKVKVPVAVLVJXFXGWOYHYJTZXGWOUIXFYFHQZYMXGXSWOYNYBYCXSWOYNYDXMAEF
        HIKVMVNVQYFBDEFGXAHIJKLMNVOVRVSXIYIXPXASXGWOYIXPTXFABDEFGXBHIJKLMNVTWAW
        BWGWCXDWQXKWSXLXDWPXJBDCXCAEWDVJCXCWRSWDWEWHWIWJWKWLWM $.
    $}

    ${
      $d w B $.  $d x F $.  $d w K $.  $d w P $.  $d w S $.  $d w U $.
      $d w X $.  $d w x A $.
      ipasslem7.a $e |- A e. X $.
      ipasslem7.b $e |- B e. X $.
      ipasslem7.f $e |- F = ( w e. RR |->
                              ( ( ( w S A ) P B ) - ( w x. ( A P B ) ) ) ) $.
      ${
        ipasslem7.j $e |- J = ( topGen ` ran (,) ) $.
        ipasslem7.k $e |- K = ( TopOpen ` CCfld ) $.
        $( Lemma for ~ ipassi .  Show that
           ` ( ( w S A ) P B ) - ( w x. ( A P B ) ) ` is continuous on ` RR ` .
           (Contributed by NM, 23-Aug-2007.)  (Revised by Mario Carneiro,
           6-May-2014.)  (New usage is discouraged.) $)
        ipasslem7 $p |- F e. ( J Cn K ) $=
          ( cr cv co cmul cmin cmpt ccn wcel wtru cioo crn ctg cfv crest tgioo2
          cc eqtri ctopon cnfldtopon a1i wss ax-resscn cims cmopn cnmptid cxmet
          cnv phnvi eqid imsxmet ax-mp mopntopon mp1i cnmptc ctx cnmpt12f dipcn
          smcn dipcl mp3an mulcn subcn cnmpt1res mptru eqeltri ) GAUBAUCZBEUDZC
          DUDZWGBCDUDZUEUDZUFUDZUGZIJUHUDZSWMWNUIUJAWLJIJUQUBIUKULUMUNJUBUOUDTJ
          UAUPURJUQUSUNUIUJJUAUTVAZUBUQVBUJVCVAUJAWIWKUFJJJJUQWOUJAWHCDJFVDUNZV
          EUNZWQJUQWOUJAWGBEJJWQWQUQWOUJAJUQWOVFZUJABJWQUQKWOWPKVGUNUIZWQKUSUNU
          IUJFVHUIZWSFPVIZWPFKLWPVJZVKVLWPWQKWQVJZVMVNZBKUIZUJQVAVOWTEJWQVPUDWQ
          UHUDUIUJXAWPEFWQJXBXCNUAVSVNVQUJACJWQUQKWOXDCKUIZUJRVAVOWTDWQWQVPUDJU
          HUDUIUJXAWPDFWQJOXBXCUAVRVNVQUJAWGWJUEJJJJUQWOWRUJAWJJJUQUQWOWOWJUQUI
          ZUJWTXEXFXGXAQRBCDFKLOVTWAVAVOUEJJVPUDJUHUDZUIUJJUAWBVAVQUFXHUIUJJUAW
          CVAVQWDWEWF $.
      $}

      $( Lemma for ~ ipassi .  By ~ ipasslem5 , ` F ` is 0 for all ` QQ ` ;
         since it is continuous and ` QQ ` is dense in ` RR ` by ~ qdensere2 ,
         we conclude ` F ` is 0 for all ` RR ` .  (Contributed by NM,
         24-Aug-2007.)  (Revised by Mario Carneiro, 6-May-2014.)
         (New usage is discouraged.) $)
      ipasslem8 $p |- F : RR --> { 0 } $=
        ( wcel cq co vx cc0 cc ccnv csn cima wss cioo crn ctg cfv ccl cr wf 0cn
        wceq cv wral cmul cmin qre oveq1 oveq1d oveq12d ovex fvmpt syl wa phnvi
        qcn cnv nvscl mp3an1 sylan dipcl mp3an13 ipasslem5 subeq0bd mpan2 eqtrd
        rgen wfun cdm wb funmpt2 qssre dmmpti sseqtrri funconstss mpbi qdensere
        mp2an ccnfld ctopn ct1 ccn w3a cha eqid cnfldhaus haust1 ax-mp uniretop
        ipasslem7 cnfldtopon toponunii dnsconst mpanl12 mp3an ) UBUCRZSGUDUBUEZ
        UFUGZSUHUIUJUKZULUKUKUMUPZUMXKGUNZUOUAUQZGUKZUBUPZUASURZXLXRUASXPSRZXQX
        PBETZCDTZXPBCDTZUSTZUTTZUBXTXPUMRXQYEUPXPVAAXPAUQZBETZCDTZYFYCUSTZUTTZY
        EUMGYFXPUPZYHYBYIYDUTYKYGYACDYFXPBEVBVCYFXPYCUSVBVDQYBYDUTVEVFVGXTBIRZY
        EUBUPOXTYLVHZYBYDYMYAIRZYBUCRZXTXPUCRZYLYNXPVJFVKRZYPYLYNFNVIZXPBEFIJLV
        LVMVNYQYNCIRYOYRPYACDFIJMVOVPVGBCXPDEFHIJKLMNPVQVRVSVTWAGWBSGWCZUGXSXLW
        DAUMYJGQWESUMYSWFAUMYJGYHYIUTVEQWGWHUASUBGWIWLWJWKWMWNUKZWORZGXMYTWPTRX
        JXLXNWQXOYTWRRUUAYTYTWSZWTYTXAXBABCDEFGHXMYTIJKLMNOPQXMWSUUBXDSUBGXMYTU
        MUCXCUCYTYTUUBXEXFXGXHXI $.
    $}

    ${
      $d w A $.  $d w B $.  $d w C $.  $d w P $.  $d w S $.  $d w U $.
      $d w X $.
      ipasslem9.a $e |- A e. X $.
      ipasslem9.b $e |- B e. X $.
      $( Lemma for ~ ipassi .  Conclude from ~ ipasslem8 the inner product
         associative law for real numbers.  (Contributed by NM, 24-Aug-2007.)
         (New usage is discouraged.) $)
      ipasslem9 $p |- ( C e. RR ->
                  ( ( C S A ) P B ) = ( C x. ( A P B ) ) ) $=
        ( vw cr wcel co cc0 cmul cmin wceq cv cmpt cfv oveq1d oveq12d eqid ovex
        oveq1 fvmpt csn wf ipasslem8 fvconst mpan eqtr3d cc wb recn phnvi nvscl
        cnv mp3an13 dipcl syl mp3an mulcl mpan2 subeq0ad mpbid ) CQRZCAESZBDSZC
        ABDSZUASZUBSZTUCZVOVQUCZVMCPQPUDZAESZBDSZWAVPUASZUBSZUEZUFZVRTPCWEVRQWF
        WACUCZWCVOWDVQUBWHWBVNBDWACAEUKUGWACVPUAUKUHWFUIZVOVQUBUJULQTUMWFUNVMWG
        TUCPABDEFWFGHIJKLMNOWIUOQTCWFUPUQURVMCUSRZVSVTUTCVAWJVOVQWJVNHRZVOUSRZF
        VDRZWJAHRZWKFMVBZNCAEFHIKVCVEWMWKBHRZWLWOOVNBDFHILVFVEVGWJVPUSRZVQUSRWM
        WNWPWQWONOABDFHILVFVHCVPVIVJVKVGVL $.
    $}

    ${
      ipasslem10.a $e |- A e. X $.
      ipasslem10.b $e |- B e. X $.
      ipasslem10.6 $e |- N = ( normCV ` U ) $.
      $( Lemma for ~ ipassi .  Show the inner product associative law for the
         imaginary number ` _i ` .  (Contributed by NM, 24-Aug-2007.)
         (New usage is discouraged.) $)
      ipasslem10 $p |- ( ( _i S A ) P B ) = ( _i x. ( A P B ) ) $=
        ( ci co cmul wcel ccj cfv cneg c4 wceq c2 cexp c1 cmin caddc cnv ax-icn
        phnvi cc nvscl mp3an 4ipval2 4cn negicn dipcl mul12i nvgcl nvcli neg1cn
        recni sqcli subcli mulcli addcomi adddii w3a nvsass mp2an oveq1i eqtr3i
        3pm3.2i ixi oveq2i fveq2i negeqi negneg1e1 3eqtri nvsid 3eqtr3i oveq12i
        mulneg1i mulm1i negsubdi2i eqtr2i mulassi eqtr4i mulcomli mullidi eqtri
        4ne0 mulcani mpbi dipcj cjmuli cr neg1rr cjrebi cji ax-1cn mul2negi ) B
        QADRZCRZUAUBZQUCZBACRZSRZUAUBZXFBCRZQABCRZSRZXGXKUAUDXGSRZUDXKSRZUEXGXK
        UEXPBXFFRZGUBZUFUGRZBUHUCZXFDRZFRZGUBZUFUGRZUIRZQBQXFDRZFRZGUBZUFUGRZBX
        IXFDRZFRZGUBZUFUGRZUIRZSRZUJRZXQEUKTZBHTZXFHTZXPYQUEEMUMZOYRQUNTZAHTZYT
        UUAULNQADEHIKUOUPZBXFCDEFGHIJKPLUQUPXQXIUDXJSRZSRZYQUDXIXJURUSYRYSUUCXJ
        UNTUUAONBACEHILUTUPZVAYQXIBAFRZGUBZUFUGRZBYAADRZFRZGUBZUFUGRZUIRZQXTBXI
        ADRZFRZGUBZUFUGRZUIRZSRZUJRZSRZUUFYQYPYFUJRZUVCYFYPXTYEXSXSXREGHIPUUAYR
        YSYTXRHTUUAOUUDBXFEFHIJVBUPVCVEVFZYDYDYCEGHIPUUAYRYSYBHTZYCHTUUAOYRYAUN
        TZYTUVFUUAVDUUDYAXFDEHIKUOUPBYBEFHIJVBUPVCVEVFVGQYOULYJYNYIYIYHEGHIPUUA
        YRYSYGHTZYHHTUUAOYRUUBYTUVHUUAULUUDQXFDEHIKUOUPBYGEFHIJVBUPVCVEVFYMYMYL
        EGHIPUUAYRYSYKHTZYLHTUUAOYRXIUNTZYTUVIUUAUSUUDXIXFDEHIKUOUPBYKEFHIJVBUP
        VCVEVFVGVHVIUVCXIUUOSRZXIUVASRZUJRUVDXIUUOUVAUSUUJUUNUUIUUIUUHEGHIPUUAY
        RYSUUCUUHHTUUAONBAEFHIJVBUPVCVEVFZUUMUUMUULEGHIPUUAYRYSUUKHTZUULHTUUAOY
        RUVGUUCUVNUUAVDNYAADEHIKUOUPBUUKEFHIJVBUPVCVEVFZVGZQUUTULXTUUSUVEUURUUR
        UUQEGHIPUUAYRYSUUPHTZUUQHTUUAOYRUVJUUCUVQUUAUSNXIADEHIKUOUPBUUPEFHIJVBU
        PVCVEVFVGZVHVJYPUVKYFUVLUJYPQUUNUUJUIRZSRZQYASRZUUOSRZUVKYOUVSQSYJUUNYN
        UUJUIYIUUMUFUGYHUULGYGUUKBFQQSRZADRZYGUUKYRUUBUUBUUCVKUWDYGUEUUAUUBUUBU
        UCULULNVPQQADEHIKVLVMUWCYAADVQVNVOVRVSVNYMUUIUFUGYLUUHGYKABFXIQSRZADRZU
        HADRZYKAUWEUHADUWEUWCUCYAUCUHQQULULWFUWCYAVQVTWAWBZVNYRUVJUUBUUCVKUWFYK
        UEUUAUVJUUBUUCUSULNVPXIQADEHIKVLVMYRUUCUWGAUEUUANADEHIKWCVMWDVRVSVNWEVR
        UVTQYAUUOSRZSRUWBUVSUWIQSUWIUUOUCUVSUUOUVPWGUUJUUNUVMUVOWHWIVRQYAUUOULV
        DUVPWJWKUWAXIUUOSYAQXIVDULQULWGZWLVNWBYFUWEUUTSRZUVLYFUHUUTSRZUWKYFUUTU
        WLYEUUSXTUIYDUURUFUGYCUUQGYBUUPBFYAQSRZADRZYBUUPYRUVGUUBUUCVKUWNYBUEUUA
        UVGUUBUUCVDULNVPYAQADEHIKVLVMUWMXIADUWJVNVOVRVSVNVRUUTUVRWMWKUWEUHUUTSU
        WHVNWKXIQUUTUSULUVRWJWNWEWKWKUUEUVBXISYRYSUUCUUEUVBUEUUAONBACDEFGHIJKPL
        UQUPVRWKWKWKXGXKUDYRYSYTXGUNTUUAOUUDBXFCEHILUTUPXIXJUSUUGVHURWOWPWQVSYR
        YSYTXHXMUEUUAOUUDBXFCEHILWRUPXLXIUAUBZXJUAUBZSRXOXIXJUSUUGWSUWOQUWPXNSU
        WMUAUBYAUAUBZQUAUBZSRZUWOQYAQVDULWSUWMXIUAUWJVSUWSYAXISRUHQSRQUWQYAUWRX
        ISYAWTTUWQYAUEXAYAVDXBWQXCWEUHQXDULXEQULWMWBWDYRYSUUCUWPXNUEUUAONBACEHI
        LWRUPWEWNWD $.
    $}

    ${
      $d x B $.  $d x y C $.  $d x y P $.
      ipasslem11.a $e |- A e. X $.
      ipasslem11.b $e |- B e. X $.
      $( TODO - proof got longer with axcnreOLD -> cnre because
         of mulcl - is it possible to rewrite it to shorten it? $)
      $( Lemma for ~ ipassi .  Show the inner product associative law for all
         complex numbers.  (Contributed by NM, 25-Aug-2007.)
         (New usage is discouraged.) $)
      ipasslem11 $p |- ( C e. CC ->
                  ( ( C S A ) P B ) = ( C x. ( A P B ) ) ) $=
        ( wcel ci cmul co wceq vx vy cc cv caddc cr wrex cnre wa ax-icn sylancr
        recn mulcom adantl oveq2d eqeq2d cnv phnvi nvscl mp3an13 sylancl ipdiri
        syl mulcl mp3an3 syl2an ipasslem9 mp3an w3a nvsass mp3an23 oveq1d dipcl
        mpan mulass cnmcv cfv ipasslem10 oveq2i eqtr4di 3eqtr4d oveqan12d eqtrd
        eqid nvdir adddir oveq1 eqeq12d syl5ibrcom sylbid rexlimivv ) CUCPCUAUD
        ZQUBUDZRSZUESZTZUBUFUGUAUFUGCAESZBDSZCABDSZRSZTZUAUBCUHWPXAUAUBUFUFWLUF
        PZWMUFPZUIZWPCWLWMQRSZUESZTZXAXDWOXFCXDWNXEWLUEXCWNXETZXBXCQUCPZWMUCPZX
        HUJWMULZQWMUMUKUNUOUPXDXAXGXFAESZBDSZXFWSRSZTXDWLAESZXEAESZGSZBDSZWLWSR
        SZXEWSRSZUESZXMXNXDXRXOBDSZXPBDSZUESZYAXBXOHPZXPHPZXRYDTZXCXBWLUCPZYEWL
        ULZFUQPZYHAHPZYEFMURZNWLAEFHIKUSUTVCXCXEUCPZYFXCXJXIYMXKUJWMQVDVAZYJYMY
        KYFYLNXEAEFHIKUSUTVCYEYFBHPZYGOXOXPBDEFGHIJKLMVBVEVFXBXCYBXSYCXTUEABWLD
        EFGHIJKLMNOVGXCWMQAESZESZBDSWMYPBDSZRSZYCXTYPBWMDEFGHIJKLMYJXIYKYPHPYLU
        JNQAEFHIKUSVHOVGXCXPYQBDXCXJXPYQTZXKXJXIYKYTUJNYJXJXIYKVIYTYLWMQAEFHIKV
        JVNVKVCVLXCXTWMQWSRSZRSZYSXCXJXTUUBTZXKXJXIWSUCPZUUCUJYJYKYOUUDYLNOABDF
        HILVMVHZWMQWSVOVKVCYRUUAWMRABDEFGFVPVQZHIJKLMNOUUFWDVRVSVTWAWBWCXDXLXQB
        DXBYHYMXLXQTZXCYIYNYHYMYKUUGNYJYHYMYKVIUUGYLWLXEAEFGHIJKWEVNVEVFVLXBYHY
        MXNYATZXCYIYNYHYMUUDUUHUUEWLXEWSWFVEVFWAXGWRXMWTXNXGWQXLBDCXFAEWGVLCXFW
        SRWGWHWIWJWKVC $.
    $}

    $( Associative law for inner product.  Equation I2 of [Ponnusamy] p. 363.
       (Contributed by NM, 25-Aug-2007.)  (New usage is discouraged.) $)
    ipassi $p |- ( ( A e. CC /\ B e. X /\ C e. X ) ->
                  ( ( A S B ) P C ) = ( A x. ( B P C ) ) ) $=
      ( wcel co cmul wceq wi cif oveq2 cc cn0v cfv oveq1d oveq2d eqeq12d imbi2d
      wa oveq1 eqid elimph ipasslem11 dedth2h com12 3impib ) AUANZBHNZCHNZABEOZ
      CDOZABCDOZPOZQZUQURUHUPVCUQURUPVCRUPAUQBFUBUCZSZEOZCDOZAVECDOZPOZQZRUPVFU
      RCVDSZDOZAVEVKDOZPOZQZRBCVDVDBVEQZVCVJUPVPUTVGVBVIVPUSVFCDBVEAETUDVPVAVHA
      PBVECDUIUEUFUGCVKQZVJVOUPVQVGVLVIVNCVKVFDTVQVHVMAPCVKVEDTUEUFUGVEVKADEFGH
      IJKLMBFHVDIVDUJZMUKCFHVDIVRMUKULUMUNUO $.
  $}

  ${
    dipdir.1 $e |- X = ( BaseSet ` U ) $.
    dipdir.2 $e |- G = ( +v ` U ) $.
    dipdir.7 $e |- P = ( .iOLD ` U ) $.
    $( Distributive law for inner product.  Equation I3 of [Ponnusamy] p. 362.
       (Contributed by NM, 25-Aug-2007.)  (New usage is discouraged.) $)
    dipdir $p |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( ( A G B ) P C ) = ( ( A P C ) + ( B P C ) ) ) $=
      ( wcel co caddc wceq cba cfv cpv cdip oveqd eqid ccphlo w3a cmul cop cabs
      wi cif fveq2 eqtrid eleq2d 3anbi123d oveq1d eqtrd oveq12d eqeq12d imbi12d
      cns elimphu ipdiri dedth imp ) EUAKZAGKZBGKZCGKZUBZABFLZCDLZACDLZBCDLZMLZ
      NZVBVFVLUFAVBEMUCUDUEUDZUGZOPZKZBVOKZCVOKZUBZABVNQPZLZCVNRPZLZACWBLZBCWBL
      ZMLZNZUFEVMEVNNZVFVSVLWGWHVCVPVDVQVEVRWHGVOAWHGEOPVOHEVNOUHUIZUJWHGVOBWIU
      JWHGVOCWIUJUKWHVHWCVKWFWHVHWACDLWCWHVGWACDWHFVTABWHFEQPVTIEVNQUHUISULWHDW
      BWACWHDERPWBJEVNRUHUIZSUMWHVIWDVJWEMWHDWBACWJSWHDWBBCWJSUNUOUPABCWBVNUQPZ
      VNVTVOVOTVTTWKTWBTEURUSUTVA $.

    $( Distributive law for inner product.  (Contributed by NM, 20-Nov-2007.)
       (New usage is discouraged.) $)
    dipdi $p |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( A P ( B G C ) ) = ( ( A P B ) + ( A P C ) ) ) $=
      ( wcel w3a co caddc wceq id wa ccj cfv dipcj ccphlo 3com13 cnv phnv simpl
      3com12 dipdir sylan2 fveq2d nvgcl 3com23 3adant3r3 syl3anc sylan cc dipcl
      simpr3 3adant3r1 3adant3r2 cjaddd oveq12d eqtrd 3eqtr3d ) AGKZBGKZCGKZLEU
      AKZVFVEVDLZABCFMZDMZABDMZACDMZNMZOVFVEVDVHVHPUBVGVHQZVIADMZRSZBADMZCADMZN
      MZRSZVJVMVNVOVSRVHVGVEVFVDLZVOVSOVEVFVDWAWAPUFBCADEFGHIJUGUHUIVGEUCKZVHVP
      VJOZEUDZWBVHQZWBVIGKZVDWCWBVHUEWBVFVEWFVDWBVEVFWFBCEFGHIUJUKULWBVFVEVDUQV
      IADEGHJTUMUNVGWBVHVTVMOWDWEVTVQRSZVRRSZNMVMWEVQVRWBVEVDVQUOKVFBADEGHJUPUR
      WBVFVDVRUOKVECADEGHJUPUSUTWEWGVKWHVLNWBVEVDWGVKOVFBADEGHJTURWBVFVDWHVLOVE
      CADEGHJTUSVAVBUNVCUH $.
  $}

  ${
    ip2dii.1 $e |- X = ( BaseSet ` U ) $.
    ip2dii.2 $e |- G = ( +v ` U ) $.
    ip2dii.7 $e |- P = ( .iOLD ` U ) $.
    ip2dii.u $e |- U e. CPreHilOLD $.
    ip2dii.a $e |- A e. X $.
    ip2dii.b $e |- B e. X $.
    ip2dii.c $e |- C e. X $.
    ip2dii.d $e |- D e. X $.
    $( Inner product of two sums.  (Contributed by NM, 17-Apr-2008.)
       (New usage is discouraged.) $)
    ip2dii $p |- ( ( A G B ) P ( C G D ) )
                = ( ( ( A P C ) + ( B P D ) ) + ( ( A P D ) + ( B P C ) ) ) $=
      ( co caddc wcel mp3an ccphlo wceq 3pm3.2i dipdi mp2an oveq12i phnvi nvgcl
      w3a cnv dipdir cc dipcl add42i 3eqtr4i ) ACDGQZEQZBUPEQZRQZACEQZADEQZRQZB
      CEQZBDEQZRQZRQABGQUPEQZUTVDRQVAVCRQRQUQVBURVERFUASZAHSZCHSZDHSZUIUQVBUBLV
      HVIVJMOPUCACDEFGHIJKUDUEVGBHSZVIVJUIURVEUBLVKVIVJNOPUCBCDEFGHIJKUDUEUFVGV
      HVKUPHSZUIVFUSUBLVHVKVLMNFUJSZVIVJVLFLUGZOPCDFGHIJUHTUCABUPEFGHIJKUKUEUTV
      DVAVCVMVHVIUTULSVNMOACEFHIKUMTVMVKVJVDULSVNNPBDEFHIKUMTVMVHVJVAULSVNMPADE
      FHIKUMTVMVKVIVCULSVNNOBCEFHIKUMTUNUO $.
  $}

  ${
    ipass.1 $e |- X = ( BaseSet ` U ) $.
    ipass.4 $e |- S = ( .sOLD ` U ) $.
    ipass.7 $e |- P = ( .iOLD ` U ) $.
    $( Associative law for inner product.  Equation I2 of [Ponnusamy] p. 363.
       (Contributed by NM, 25-Aug-2007.)  (New usage is discouraged.) $)
    dipass $p |- ( ( U e. CPreHilOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
                 ( ( A S B ) P C ) = ( A x. ( B P C ) ) ) $=
      ( wcel co cmul wceq cba cfv cns cdip fveq2 eqid ccphlo cc w3a wi cop cabs
      caddc cif eqtrid eleq2d oveqd oveq1d eqtrd oveq2d eqeq12d imbi12d elimphu
      3anbi23d cpv ipassi dedth imp ) FUAKZAUBKZBGKZCGKZUCZABELZCDLZABCDLZMLZNZ
      VCVGVLUDVDBVCFUGMUEUFUEZUHZOPZKZCVOKZUCZABVNQPZLZCVNRPZLZABCWALZMLZNZUDFV
      MFVNNZVGVRVLWEWFVEVPVFVQVDWFGVOBWFGFOPVOHFVNOSUIZUJWFGVOCWGUJURWFVIWBVKWD
      WFVIVTCDLWBWFVHVTCDWFEVSABWFEFQPVSIFVNQSUIUKULWFDWAVTCWFDFRPWAJFVNRSUIZUK
      UMWFVJWCAMWFDWABCWHUKUNUOUPABCWAVSVNVNUSPZVOVOTWITVSTWATFUQUTVAVB $.

    $( "Associative" law for second argument of inner product (compare
       ~ dipass ).  (Contributed by NM, 22-Nov-2007.)
       (New usage is discouraged.) $)
    dipassr $p |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. CC /\ C e. X ) ) ->
                 ( A P ( B S C ) ) = ( ( * ` B ) x. ( A P C ) ) ) $=
      ( wcel cc w3a wa co ccj cfv cmul wceq dipcj ccphlo 3anrot dipass cnv phnv
      sylan2b fveq2d simpl nvscl 3adant3r1 simpr1 syl3anc sylan dipcl 3adant3r2
      simpr2 3com23 cjmuld oveq2d eqtrd 3eqtr3d ) FUAKZAGKZBLKZCGKZMZNZBCEOZADO
      ZPQZBCADOZROZPQZAVHDOZBPQZACDOZROZVGVIVLPVFVBVDVEVCMVIVLSVCVDVEUBBCADEFGH
      IJUCUFUGVBFUDKZVFVJVNSZFUEZVRVFNZVRVHGKZVCVSVRVFUHVRVDVEWBVCBCEFGHIUIUJVR
      VCVDVEUKVHADFGHJTULUMVBVRVFVMVQSVTWAVMVOVKPQZROVQWABVKVRVCVDVEUPVRVCVEVKL
      KZVDVRVEVCWDCADFGHJUNUQUOURWAWCVPVORVRVCVEWCVPSZVDVRVEVCWECADFGHJTUQUOUSU
      TUMVA $.

    $( "Associative" law for inner product.  Conjugate version of ~ dipassr .
       (Contributed by NM, 23-Nov-2007.)  (New usage is discouraged.) $)
    dipassr2 $p |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. CC /\ C e. X ) ) ->
                 ( A P ( ( * ` B ) S C ) ) = ( B x. ( A P C ) ) ) $=
      ( ccphlo wcel cc w3a wa ccj cfv co cmul wceq cjcl dipassr syl3anr2 adantl
      cjcj 3ad2ant2 oveq1d eqtrd ) FKLZAGLZBMLZCGLZNZOZABPQZCERDRZUOPQZACDRZSRZ
      BURSRUKUJUIUOMLULUPUSTBUAAUOCDEFGHIJUBUCUNUQBURSUMUQBTZUIUKUJUTULBUEUFUDU
      GUH $.
  $}

  ${
    ipsubdir.1 $e |- X = ( BaseSet ` U ) $.
    ipsubdir.3 $e |- M = ( -v ` U ) $.
    ipsubdir.7 $e |- P = ( .iOLD ` U ) $.
    $( Distributive law for inner product subtraction.  (Contributed by NM,
       20-Nov-2007.)  (New usage is discouraged.) $)
    dipsubdir $p |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( ( A M B ) P C ) = ( ( A P C ) - ( B P C ) ) ) $=
      ( wcel w3a wa cneg cfv co caddc wceq cc sylan ccphlo cns cpv cmin idd cnv
      c1 phnv neg1cn nvscl mp3an2 ex 3anim123d imp dipdir syldan nvmval syl3an1
      eqid 3adant3r3 oveq1d cmul dipass mp3anr1 dipcl 3expb mulm1d eqtrd oveq2d
      3adantr1 3adant3r2 3adant3r1 negsubd eqtr2d 3eqtr4d ) EUAKZAGKZBGKZCGKZLZ
      MZAUGNZBEUBOZPZEUCOZPZCDPZACDPZWDCDPZQPZABFPZCDPWHBCDPZUDPZVPVTVQWDGKZVSL
      ZWGWJRVPVTWOVPVQVQVRWNVSVSVPVQUEVPVRWNVPEUFKZVRWNEUHZWPWBSKZVRWNUIWBBWCEG
      HWCUSZUJUKTULVPVSUEUMUNAWDCDEWEGHWEUSZJUOUPWAWKWFCDVPVQVRWKWFRZVSVPWPVQVR
      XAWQABWCEWEFGHWTWSIUQURUTVAWAWJWHWLNZQPZWMWAWIXBWHQVPVRVSWIXBRVQVPVRVSMZM
      ZWIWBWLVBPZXBVPWRVRVSWIXFRUIWBBCDWCEGHWSJVCVDXEWLVPWPXDWLSKZWQWPVRVSXGBCD
      EGHJVEZVFTVGVHVJVIVPWPVTXCWMRWQWPVTMWHWLWPVQVSWHSKVRACDEGHJVEVKWPVRVSXGVQ
      XHVLVMTVNVO $.

    $( Distributive law for inner product subtraction.  (Contributed by NM,
       20-Nov-2007.)  (New usage is discouraged.) $)
    dipsubdi $p |- ( ( U e. CPreHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                 ( A P ( B M C ) ) = ( ( A P B ) - ( A P C ) ) ) $=
      ( wcel w3a co cmin wceq id wa ccj cfv dipcj ccphlo 3com13 3com12 cnv phnv
      dipsubdir sylan2 fveq2d simpl nvmcl 3com23 3adant3r3 simpr3 syl3anc sylan
      cc dipcl 3adant3r1 3adant3r2 cjsub syl2anc oveq12d eqtrd 3eqtr3d ) AGKZBG
      KZCGKZLEUAKZVGVFVELZABCFMZDMZABDMZACDMZNMZOVGVFVEVIVIPUBVHVIQZVJADMZRSZBA
      DMZCADMZNMZRSZVKVNVOVPVTRVIVHVFVGVELZVPVTOVFVGVEWBWBPUCBCADEFGHIJUFUGUHVH
      EUDKZVIVQVKOZEUEZWCVIQZWCVJGKZVEWDWCVIUIWCVGVFWGVEWCVFVGWGBCEFGHIUJUKULWC
      VGVFVEUMVJADEGHJTUNUOVHWCVIWAVNOWEWFWAVRRSZVSRSZNMZVNWFVRUPKZVSUPKZWAWJOW
      CVFVEWKVGBADEGHJUQURWCVGVEWLVFCADEGHJUQUSVRVSUTVAWFWHVLWIVMNWCVFVEWHVLOVG
      BADEGHJTURWCVGVEWIVMOVFCADEGHJTUSVBVCUOVDUG $.
  $}

  ${
    pyth.1 $e |- X = ( BaseSet ` U ) $.
    pyth.2 $e |- G = ( +v ` U ) $.
    pyth.6 $e |- N = ( normCV ` U ) $.
    pyth.7 $e |- P = ( .iOLD ` U ) $.
    pythi.u $e |- U e. CPreHilOLD $.
    pythi.a $e |- A e. X $.
    pythi.b $e |- B e. X $.
    $( The Pythagorean theorem for an arbitrary complex inner product
       (pre-Hilbert) space ` U ` .  The square of the norm of the sum of two
       orthogonal vectors (i.e. whose inner product is 0) is the sum of the
       squares of their norms.  Problem 2 in [Kreyszig] p. 135.  (Contributed
       by NM, 17-Apr-2008.)  (New usage is discouraged.) $)
    pythi $p |- ( ( A P B ) = 0 -> ( ( N ` ( A G B ) ) ^ 2 )
        = ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) $=
      ( co cc0 wceq caddc wcel mp3an cfv c2 cexp ip2dii id cnv phnvi diporthcom
      wb biimpi oveq12d 00id eqtrdi oveq2d cc dipcl addcli addridi eqtrid nvgcl
      ipidsq mp2an oveq12i 3eqtr3g ) ABCOZPQZABEOZVGCOZAACOZBBCOZROZVGFUAUBUCOZ
      AFUAUBUCOZBFUAUBUCOZROVFVHVKVEBACOZROZROZVKABABCDEGHIKLMNMNUDVFVQVKPROVKV
      FVPPVKRVFVPPPROPVFVEPVOPRVFUEVFVOPQZDUFSZAGSZBGSZVFVRUIDLUGZMNABCDGHKUHTU
      JUKULUMUNVKVIVJVSVTVTVIUOSWBMMAACDGHKUPTVSWAWAVJUOSWBNNBBCDGHKUPTUQURUMUS
      VSVGGSZVHVLQWBVSVTWAWCWBMNABDEGHIUTTVGCDFGHJKVAVBVIVMVJVNRVSVTVIVMQWBMACD
      FGHJKVAVBVSWAVJVNQWBNBCDFGHJKVAVBVCVD $.
  $}

  ${
    siii.1 $e |- X = ( BaseSet ` U ) $.
    siii.6 $e |- N = ( normCV ` U ) $.
    siii.7 $e |- P = ( .iOLD ` U ) $.
    siii.9 $e |- U e. CPreHilOLD $.
    siii.a $e |- A e. X $.
    siii.b $e |- B e. X $.
    ${
      sii1.3 $e |- M = ( -v ` U ) $.
      sii1.4 $e |- S = ( .sOLD ` U ) $.
      sii1.c $e |- C e. CC $.
      sii1.r $e |- ( C x. ( A P B ) ) e. RR $.
      sii1.z $e |- 0 <_ ( C x. ( A P B ) ) $.
      $( Lemma for ~ sii .  (Contributed by NM, 23-Nov-2007.)
         (New usage is discouraged.) $)
      siilem1 $p |- ( ( B P A ) = ( C x. ( ( N ` B ) ^ 2 ) ) ->
                ( sqrt ` ( ( A P B ) x. ( C x. ( ( N ` B ) ^ 2 ) ) ) ) <_
                       ( ( N ` A ) x. ( N ` B ) ) ) $=
        ( co cfv c2 cexp cmul wceq csqrt cle wbr cc0 cmin ccj phnvi cnv wcel cc
        cjcli nvscl mp3an nvmcl nvcli sqge0i ccphlo w3a 3pm3.2i dipsubdi ipidsq
        mp2an dipass oveq2i eqtri recni sqcli dipcl mulcli sub4 mp4an dipsubdir
        oveq12i oveq1i subdii 3eqtr4i 3eqtr3i oveq2 mul01i eqtrdi sylbir oveq2d
        dipassr2 breqtri subeq0i resqcli subcli subid1i breqtrid subge0i pm3.2i
        sylib cr wa lemul1a mpan syl breqtrrdi mulge0i remulcli sqrtlei mulcomi
        sqmuli wb mulassi fveq2i nvge0 sqrtsqi ax-mp 3brtr3g ) BADUAZCBHUBZUCUD
        UAZUEUAZUFZCABDUAZUEUAZXSUEUAZUGUBZAHUBZXRUEUAZUCUDUAZUGUBZYBXTUEUAZUGU
        BYGUHYAYDYHUHUIZYEYIUHUIZYAYDYFUCUDUAZXSUEUAZYHUHYAYCYMUHUIZYDYNUHUIZYA
        UJYMYCUKUAZUHUIYOYAUJYQCULUBZXQXTUKUAZUEUAZUKUAZYQUHUJAYRBEUAZGUAZHUBZU
        CUDUAZUUAUHUUDUUCFHIJKFMUMZFUNUOZAIUOZUUBIUOZUUCIUOZUUFNUUGYRUPUOZBIUOZ
        UUIUUFCRUQZOYRBEFIJQURUSZAUUBFGIJPUTUSZVAVBUUCUUCDUAZUUCADUAZUUCUUBDUAZ
        UKUAZUUEUUAFVCUOZUUJUUHUUIVDUUPUUSUFMUUJUUHUUIUUONUUNVEUUCAUUBDFGIJPLVF
        VHUUGUUJUUPUUEUFUUFUUOUUCDFHIJKLVGVHYMYRXQUEUAZUKUAZYCUUBUUBDUAZUKUAZUK
        UAZYQUVAYRXTUEUAZUKUAZUKUAZUUSUUAUVEUVBYCUVFUKUAZUKUAZUVHUVDUVIUVBUKUVC
        UVFYCUKUVCYRBUUBDUAZUEUAZUVFUUTUUKUULUUIVDUVCUVLUFMUUKUULUUIUUMOUUNVEYR
        BUUBDEFIJQLVIVHUVKXTYRUEUVKCBBDUAZUEUAZXTUUTUULCUPUOZUULVDUVKUVNUFMUULU
        VOUULOROVEBCBDEFIJQLWIVHUVMXSCUEUUGUULUVMXSUFUUFOBDFHIJKLVGVHVJVKVJVKVJ
        VJYMUPUOUVAUPUOYCUPUOUVFUPUOUVJUVHUFYFYFAFHIJKUUFNVAZVLZVMYRXQUUMUUGUUL
        UUHXQUPUOUUFONBADFIJLVNUSZVOYCSVLZYRXTUUMCXSRXRXRBFHIJKUUFOVAZVLZVMVOZV
        OYMUVAYCUVFVPVQVKUUQUVBUURUVDUKUUQAADUAZUUBADUAZUKUAZUVBUUTUUHUUIUUHVDU
        UQUWEUFMUUHUUIUUHNUUNNVEAUUBADFGIJPLVRVHUWCYMUWDUVAUKUUGUUHUWCYMUFUUFNA
        DFHIJKLVGVHUUTUUKUULUUHVDUWDUVAUFMUUKUULUUHUUMONVEYRBADEFIJQLVIVHVSVKUU
        RAUUBDUAZUVCUKUAZUVDUUTUUHUUIUUIVDUURUWGUFMUUHUUIUUINUUNUUNVEAUUBUUBDFG
        IJPLVRVHUWFYCUVCUKUUTUUHUVOUULVDUWFYCUFMUUHUVOUULNROVEACBDEFIJQLWIVHVTV
        KVSYTUVGYQUKYRXQXTUUMUVRUWBWAVJWBWCWJYAUUAYQUJUKUAYQYAYTUJYQUKYAYSUJUFZ
        YTUJUFXQXTUVRUWBWKUWHYTYRUJUEUAUJYSUJYRUEWDYRUUMWEWFWGWHYQYMYCYMYFUVPWL
        ZVLUVSWMWNWFWOYMYCUWISWPWRYCWSUOZYMWSUOZXSWSUOZUJXSUHUIZWTZVDYOYPUWJUWK
        UWNSUWIUWLUWMXRUVTWLZXRUVTVBZWQVEYCYMXSXAXBXCYFXRUVQUWAXIXDUJYDUHUIZUJY
        HUHUIYKYLXJUJYCUHUIUWMUWQTUWPYCXSSUWOXEVHYGYFXRUVPUVTXFZVBYDYHYCXSSUWOX
        FYGUWRWLXGVHWRYDYJUGYDYBCUEUAZXSUEUAYJYCUWSXSUECYBRUUGUUHUULYBUPUOUUFNO
        ABDFIJLVNUSZXHVTYBCXSUWTRXSUWOVLXKVKXLUJYGUHUIZYIYGUFUJYFUHUIZUJXRUHUIZ
        UXAUUGUUHUXBUUFNAFHIJKXMVHUUGUULUXCUUFOBFHIJKXMVHYFXRUVPUVTXEVHYGUWRXNX
        OXP $.
    $}

    ${
      siii2.3 $e |- M = ( -v ` U ) $.
      siii2.4 $e |- S = ( .sOLD ` U ) $.
      $( Lemma for ~ sii .  (Contributed by NM, 24-Nov-2007.)
         (New usage is discouraged.) $)
      siilem2 $p |- ( ( C e. CC /\ ( C x. ( A P B ) ) e. RR /\
                           0 <_ ( C x. ( A P B ) ) ) ->
                ( ( B P A ) = ( C x. ( ( N ` B ) ^ 2 ) ) ->
                  ( sqrt ` ( ( A P B ) x. ( C x. ( ( N ` B ) ^ 2 ) ) ) ) <_
                         ( ( N ` A ) x. ( N ` B ) ) ) ) $=
        ( co cmul cc0 cc wcel cr cle wbr w3a c2 cexp wceq csqrt wi oveq1 eqeq2d
        cfv cif oveq2d fveq2d breq1d imbi12d eleq1 eleq1d 3anbi123d phnvi dipcl
        breq2d 0cn cnv mp3an mul02i 0re eqeltri breqtrri 3pm3.2i elimhyp simp1i
        0le0 simp2i simp3i siilem1 dedth ) CUAUBZCABDRZSRZUCUBZTWCUDUEZUFZBADRZ
        CBHUNZUGUHRZSRZUIZWBWJSRZUJUNZAHUNWHSRZUDUEZUKWGWFCTUOZWISRZUIZWBWQSRZU
        JUNZWNUDUEZUKCTCWPUIZWKWRWOXAXBWJWQWGCWPWISULZUMXBWMWTWNUDXBWLWSUJXBWJW
        QWBSXCUPUQURUSABWPDEFGHIJKLMNOPQWPUAUBZWPWBSRZUCUBZTXEUDUEZWFXDXFXGUFTU
        AUBZTWBSRZUCUBZTXIUDUEZUFCTXBWAXDWDXFWEXGCWPUAUTXBWCXEUCCWPWBSULZVAXBWC
        XETUDXLVEVBTWPUIZXHXDXJXFXKXGTWPUAUTXMXIXEUCTWPWBSULZVAXMXIXETUDXNVEVBX
        HXJXKVFXITUCWBFVGUBAIUBBIUBWBUAUBFMVCNOABDFIJLVDVHVIZVJVKTTXIUDVPXOVLVM
        VNZVOXDXFXGXPVQXDXFXGXPVRVSVT $.
    $}

    $( Inference from ~ sii .  (Contributed by NM, 20-Nov-2007.)
       (New usage is discouraged.) $)
    siii $p |- ( abs ` ( A P B ) ) <_ ( ( N ` A ) x. ( N ` B ) ) $=
      ( co cfv cmul cle wbr wceq cc0 wcel cabs cn0v oveq2 cnv phnvi dip0r mp2an
      eqid eqtrdi abs00bd nvge0 nvcli mulge0i eqbrtrdi wne c2 cexp csqrt ccj cc
      cdiv dipcl mp3an absval ax-mp recni sqeq0i wb nvz bitri necon3bii resqcli
      divcan1zi sylbir dipcj eqtr4di oveq2d fveq2d eqtr4id eqcomd cr wi divclzi
      wa div23 mp3an12 mpan ipipcj mulcomli oveq1i eqtr3di abscli redivclzi clt
      eqeltrd sqgt0i sqge0i divge0 mpanl12 sylancr breqtrrd cns siilem2 syl3anc
      cnsb mpd eqbrtrd pm2.61ine ) ABCMZUANZAENZBENZOMZPQBDUBNZBXNRZXJSXMPXOXIX
      OXIAXNCMZSBXNACUCDUDTZAFTZXPSRDJUEZKACDFXNGXNUHZIUFUGUIUJSXKPQZSXLPQZSXMP
      QXQXRYAXSKADEFGHUKUGXQBFTZYBXSLBDEFGHUKUGXKXLADEFGHXSKULBDEFGHXSLULZUMUGU
      NBXNUOZXJXIBACMZXLUPUQMZVAMZYGOMZOMZURNZXMPYEXJXIXIUSNZOMZURNZYKXIUTTZXJY
      NRXQXRYCYOXSKLABCDFGIVBVCZXIVDVEYEYJYMURYEYIYLXIOYEYIYFYLYEYGSUOZYIYFRYGS
      BXNYGSRXLSRZXOXLXLYDVFVGXQYCYRXOVHXSLBDEFXNGXTHVIUGZVJVKZYFYGXQYCXRYFUTTZ
      XSLKBACDFGIVBVCZYGXLYDVLZVFZVMVNZXQXRYCYLYFRXSKLABCDFGIVOVCVPVQVRVSYEYFYI
      RZYKXMPQZYEYIYFUUEVTYEYHUTTZYHXIOMZWATSUUIPQUUFUUGWBYEYQUUHYTYFYGUUBUUDWC
      VNYEUUIXJUPUQMZYGVAMZWAYEYFXIOMZYGVAMZUUIUUKYEYQUUMUUIRZYTYGUTTZYQUUNUUDU
      UAYOUUOYQWDUUNUUBYPYFXIYGWEWFWGVNUULUUJYGVAXIYFUUJYPUUBXQXRYCXIYFOMUUJRXS
      KLABCDFGIWHVCWIWJWKZYEYQUUKWATYTUUJYGXJXIYPWLZVLZUUCWMVNWOYESUUKUUIPYEYGW
      ATZSYGWNQZSUUKPQZUUCYEXLSUOUUTXLSBXNYSVKXLYDWPVNUUJWATSUUJPQUUSUUTWDUVAUU
      RXJUUQWQUUJYGWRWSWTUUPXAABYHCDXBNZDDXENZEFGHIJKLUVCUHUVBUHXCXDXFXGXH $.
  $}

  ${
    sii.1 $e |- X = ( BaseSet ` U ) $.
    sii.6 $e |- N = ( normCV ` U ) $.
    sii.7 $e |- P = ( .iOLD ` U ) $.
    sii.9 $e |- U e. CPreHilOLD $.
    $( Obsolete version of ~ ipcau as of 22-Sep-2024.  Schwarz inequality.
       Part of Lemma 3-2.1(a) of [Kreyszig] p. 137.  This is also called the
       Cauchy-Schwarz inequality by some authors and
       Bunjakovaskij-Cauchy-Schwarz inequality by others.  See also Theorems
       ~ bcseqi , ~ bcsiALT , ~ bcsiHIL , ~ csbren .  (Contributed by NM,
       12-Jan-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    sii $p |- ( ( A e. X /\ B e. X ) ->
               ( abs ` ( A P B ) ) <_ ( ( N ` A ) x. ( N ` B ) ) ) $=
      ( wcel co cabs cfv cmul cle wbr cif wceq fveq2 cn0v fvoveq1 breq12d oveq2
      oveq1d fveq2d oveq2d eqid elimph siii dedth2h ) AFKZBFKZABCLMNZAENZBENZOL
      ZPQULADUANZRZBCLZMNZUSENZUPOLZPQUSUMBURRZCLZMNZVBVDENZOLZPQABURURAUSSZUNV
      AUQVCPAUSBMCUBVIUOVBUPOAUSETUEUCBVDSZVAVFVCVHPVJUTVEMBVDUSCUDUFVJUPVGVBOB
      VDETUGUCUSVDCDEFGHIJADFURGURUHZJUIBDFURGVKJUIUJUK $.
  $}

  ${
    $d w x y z A $.  $d w y z C $.  $d w y z F $.  $d w x y z U $.
    $d w x y z X $.  $d x P $.  $d z B $.
    ipblnfi.1 $e |- X = ( BaseSet ` U ) $.
    ipblnfi.7 $e |- P = ( .iOLD ` U ) $.
    ipblnfi.9 $e |- U e. CPreHilOLD $.
    ipblnfi.c $e |- C = <. <. + , x. >. , abs >. $.
    ipblnfi.l $e |- B = ( U BLnOp C ) $.
    ipblnfi.f $e |- F = ( x e. X |-> ( x P A ) ) $.
    $( A function ` F ` generated by varying the first argument of an inner
       product (with its second argument a fixed vector ` A ` ) is a bounded
       linear functional, i.e. a bounded linear operator from the vector space
       to ` CC ` .  (Contributed by NM, 12-Jan-2008.)  (Revised by Mario
       Carneiro, 19-Nov-2013.)  (New usage is discouraged.) $)
    ipblnfi $p |- ( A e. X -> F e. B ) $=
      ( vz wcel co cfv cc wceq vy vw clno cnmcv cr cv cabs cmul cle wbr wral wf
      cns cpv caddc cnv phnvi dipcl mp3an1 ancoms fmptd wa eqid nvscl ad2ant2lr
      simprr simpll ccphlo w3a dipdir syl3anc simplr simprl ipassi oveq1d eqtrd
      mpan adantll nvgcl sylan anasss oveq1 ovex fvmpt ad2antrl oveq2d ad2antll
      syl oveq12d 3eqtr4d ralrimivva ralrimiva wb cnnv cnnvba cnnvg cnnvs islno
      mp2an sylanbrc sii adantl fveq2d recnd mulcom syl2an 3brtr4d cnnvnm blo3i
      nvcl ) BHPZGFDUCQZPZBFUDRZRZUEPZOUFZGRZUGRZXOXQXNRZUHQZUIUJZOHUKGCPXKHSGU
      LZUAUFZXQFUMRZQZUBUFZFUNRZQZGRZYDXRUHQZYGGRZUOQZTZUBHUKOHUKZUASUKZXMXKAHA
      UFZBEQZSGYQHPZXKYRSPZFUPPZYSXKYTFKUQZYQBEFHIJURUSUTNVAXKYOUASXKYDSPZVBZYN
      OUBHHUUDXQHPZYGHPZVBZVBZYIBEQZYDXQBEQZUHQZYGBEQZUOQZYJYMUUHUUIYFBEQZUULUO
      QZUUMUUHYFHPZUUFXKUUIUUOTZUUCUUEUUPXKUUFUUAUUCUUEUUPUUBYDXQYEFHIYEVCZVDUS
      ZVEUUDUUEUUFVFXKUUCUUGVGZFVHPUUPUUFXKVIUUQKYFYGBEFYHHIYHVCZJVJVQVKUUHUUNU
      UKUULUOUUHUUCUUEXKUUNUUKTXKUUCUUGVLUUDUUEUUFVMUUTYDXQBEYEFYHHIUVAUURJKVNV
      KVOVPUUHYIHPZYJUUITUUDUUEUUFUVBUUDUUEVBUUPUUFUVBUUCUUEUUPXKUUSVRUUAUUPUUF
      UVBUUBYFYGFYHHIUVAVSUSVTWAAYIYRUUIHGYQYIBEWBNYIBEWCWDWHUUHYKUUKYLUULUOUUH
      XRUUJYDUHUUEXRUUJTZUUDUUFAXQYRUUJHGYQXQBEWBNXQBEWCWDZWEWFUUFYLUULTUUDUUEA
      YGYRUULHGYQYGBEWBNYGBEWCWDWGWIWJWKWLUUADUPPXMYCYPVBWMUUBDLWNZUAOUBYEUHGFY
      HUOXLDHSIDLWOUVADLWPUURDLWQXLVCZWRWSWTUUAXKXPUUBBFXNHIXNVCZXJVQZXKYBOHXKU
      UEVBZUUJUGRZXTXOUHQZXSYAUIUUEXKUVJUVKUIUJXQBEFXNHIUVGJKXAUTUVIXRUUJUGUUEU
      VCXKUVDXBXCXKXOSPXTSPYAUVKTUUEXKXOUVHXDUUEXTUUAUUEXTUEPUUBXQFXNHIUVGXJVQX
      DXOXTXEXFXGWLOXOCGFXLXNUGDHIUVGDLXHUVFMUUBUVEXIVK $.
  $}

  ${
    $d x A $.  $d x B $.  $d s t x P $.  $d s t Q $.  $d x y S $.
    $d s t x y T $.  $d x U $.  $d s t x y X $.  $d s t x y Y $.
    ip2eqi.1 $e |- X = ( BaseSet ` U ) $.
    ip2eqi.7 $e |- P = ( .iOLD ` U ) $.
    ip2eqi.u $e |- U e. CPreHilOLD $.
    $( Two vectors are equal iff their inner products with all other vectors
       are equal.  (Contributed by NM, 24-Jan-2008.)
       (New usage is discouraged.) $)
    ip2eqi $p |- ( ( A e. X /\ B e. X ) -> ( A. x e. X ( x P A
                                               ) = ( x P B ) <-> A = B ) ) $=
      ( wcel co wceq cfv eqid mp3an1 oveq1 syl cc0 mpan wb wa cv wral cnv phnvi
      cnsb wi nvmcl eqeq12d rspcv cmin cn0v simpl simpr ccphlo dipsubdi syl3anc
      w3a eqeq1d bitr3d cc dipcl syl2anc sylancom subeq0ad nvmeq0 3bitr3d oveq2
      ipz sylibd ralrimivw impbid1 ) BFJZCFJZUAZAUBZBDKZVPCDKZLZAFUCZBCLZVOVTBC
      EUFMZKZBDKZWCCDKZLZWAVOWCFJZVTWFUGEUDJZVMVNWGEIUEZBCEWBFGWBNZUHOZVSWFAWCF
      VPWCLVQWDVRWEVPWCBDPVPWCCDPUIUJQVOWDWEUKKZRLZWCEULMZLZWFWAVOWCWCDKZRLZWMW
      OVOWPWLRVOWGVMVNWPWLLZWKVMVNUMZVMVNUNEUOJWGVMVNURWRIWCBCDEWBFGWJHUPSUQUSV
      OWGWQWOTZWKWHWGWTWIWCDEFWNGWNNZHVISQUTVOWDWEVOWGVMWDVAJZWKWSWHWGVMXBWIWCB
      DEFGHVBOVCVMVNWGWEVAJZWKWHWGVNXCWIWCCDEFGHVBOVDVEWHVMVNWOWATWIBCEWBFWNGWJ
      XAVFOVGVJWAVSAFBCVPDVHVKVL $.

    $( A condition implying that two operators are equal.  (Contributed by NM,
       25-Jan-2008.)  (New usage is discouraged.) $)
    phoeqi $p |- ( ( S : Y --> X /\ T : Y --> X ) -> ( A. x e. X A. y e.
      Y ( x P ( S ` y ) ) = ( x P ( T ` y ) ) <-> S = T ) ) $=
      ( cv cfv co wceq wral wf wa wcel wb ralcom ffvelcdm anandirs ralbidva wfn
      ip2eqi syl2an ffn eqfnfv bitr4d bitrid ) ALZBLZDMZCNULUMEMZCNOZBHPAGPUPAG
      PZBHPZHGDQZHGEQZRZDEOZUPABGHUAVAURUNUOOZBHPZVBVAUQVCBHUSUTUMHSZUQVCTZUSVE
      RUNGSUOGSVFUTVERHGUMDUBHGUMEUBAUNUOCFGIJKUFUGUCUDUSDHUEEHUEVBVDTUTHGDUHHG
      EUHBHDEUIUGUJUK $.

    $( Every operator has at most one adjoint.  (Contributed by NM,
       25-Jan-2008.)  (New usage is discouraged.) $)
    ajmoi $p |- E* s ( s : Y --> X /\
           A. x e. X A. y e. Y ( ( T ` x ) Q y ) = ( x P ( s ` y ) ) ) $=
      ( vt cv wf cfv co wceq wral wa wmo wi r19.26-2 eqtr2 sylbir phoeqi biimpa
      wal 2ralimi sylan2 an4s gen2 feq1 fveq1 oveq2d 2ralbidv anbi12d mo4 mpbir
      eqeq2d ) HGINZOZANZEPBNZDQZVCVDVAPZCQZRZBHSAGSZTZIUAVJHGMNZOZVEVCVDVKPZCQ
      ZRZBHSAGSZTZTVAVKRZUBZMUHIUHVSIMVBVLVIVPVRVIVPTZVBVLTZVGVNRZBHSAGSZVRVTVH
      VOTZBHSAGSWCVHVOABGHUCWDWBABGHVEVGVNUDUIUEWAWCVRABCVAVKFGHJKLUFUGUJUKULVJ
      VQIMVRVBVLVIVPHGVAVKUMVRVHVOABGHVRVGVNVEVRVFVMVCCVDVAVKUNUOUTUPUQURUS $.
  $}

  ${
    $d s t x y U $.  $d s t x y W $.
    ajfuni.5 $e |- A = ( U adj W ) $.
    ajfuni.u $e |- U e. CPreHilOLD $.
    ajfuni.w $e |- W e. NrmCVec $.
    $( The adjoint function is a function.  (Contributed by NM, 25-Jan-2008.)
       (New usage is discouraged.) $)
    ajfuni $p |- Fun A $=
      ( vt vs vx vy wfun cba cfv cv wf cdip co wceq wral eqid w3a copab funopab
      wmo wa ajmoi 3simpc moimi ax-mp mpgbir cnv wcel phnvi ajfval mp2an funeqi
      mpbir ) AKBLMZCLMZGNZOZUSURHNZOZINZUTMJNZCPMZQVDVEVBMBPMZQRJUSSIURSZUAZGH
      UBZKZVKVIHUDZGVIGHUCVCVHUEZHUDVLIJVGVFUTBURUSHURTZVGTZEUFVIVMHVAVCVHUGUHU
      IUJAVJBUKULCUKULAVJRBEUMFIJGAVGVFBCURUSHVNUSTVOVFTDUNUOUPUQ $.
  $}

  ${
    ajfun.5 $e |- A = ( U adj W ) $.
    $( The adjoint function is a function.  This is not immediately apparent
       from ~ df-aj but results from the uniqueness shown by ~ ajmoi .
       (Contributed by NM, 26-Jan-2008.)  (New usage is discouraged.) $)
    ajfun $p |- ( ( U e. CPreHilOLD /\ W e. NrmCVec ) -> Fun A ) $=
      ( ccphlo wcel cnv wfun caddc cmul cop cabs cif caj co oveq1 eqtrid funeqd
      wceq oveq2 eqid elimphu elimnvu ajfuni dedth2h ) BEFZCGFZAHUFBIJKLKZMZCNO
      ZHUIUGCUHMZNOZHBCUHUHBUISZAUJUMABCNOUJDBUICNPQRCUKSUJULCUKUINTRULUIUKULUA
      BUBCUCUDUE $.
  $}

  ${
    $d t P $.  $d t Q $.  $d s t x y T $.  $d s t x y U $.  $d s t x y W $.
    $d s t x y X $.  $d s t y Y $.
    ajval.1 $e |- X = ( BaseSet ` U ) $.
    ajval.2 $e |- Y = ( BaseSet ` W ) $.
    ajval.3 $e |- P = ( .iOLD ` U ) $.
    ajval.4 $e |- Q = ( .iOLD ` W ) $.
    ajval.5 $e |- A = ( U adj W ) $.
    $( Value of the adjoint function.  (Contributed by NM, 25-Jan-2008.)
       (New usage is discouraged.) $)
    ajval $p |- ( ( U e. CPreHilOLD /\ W e. NrmCVec /\ T : X --> Y ) ->
       ( A ` T ) = ( iota s ( s : Y --> X /\
          A. x e. X A. y e. Y ( ( T ` x ) Q y ) = ( x P ( s ` y ) ) ) ) ) $=
      ( vt wcel cfv wceq ccphlo cnv wf w3a cv co wral copab wa cio ajfval sylan
      phnv fveq1d 3adant3 cvv cba fvexi fex mpan2 eqid feq1 fveq1 oveq1d eqeq1d
      2ralbidv 3anbi13d fvopab5 syl 3anass baib iotabidv eqtrd 3ad2ant3 ) GUARZ
      HUBRZIJFUCZUDFCSZFIJQUEZUCZJIKUEZUCZAUEZVSSZBUEZEUFZWCWEWASDUFZTZBJUGAIUG
      ZUDZQKUHZSZWBWCFSZWEEUFZWGTZBJUGAIUGZUIZKUJZVOVPVRWLTVQVOVPUIFCWKVOGUBRVP
      CWKTGUMABQCDEGHIJKLMNOPUKULUNUOVQVOWLWRTVPVQWLVQWBWPUDZKUJZWRVQFUPRZWLWTT
      VQIUPRXAIGUQLURIJUPFUSUTWJWSQKFWKUPWKVAVSFTZVTVQWIWPWBIJVSFVBXBWHWOABIJXB
      WFWNWGXBWDWMWEEWCVSFVCVDVEVFVGVHVIVQWSWQKWSVQWQVQWBWPVJVKVLVMVNVM $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Complex Banach spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CBan $.

  $( Extend class notation with the class of all complex Banach spaces. $)
  ccbn $a class CBan $.

  $( Define the class of all complex Banach spaces.  (Contributed by NM,
     5-Dec-2006.)  Use ~ df-bn instead.  (New usage is discouraged.) $)
  df-cbn $a |- CBan = { u e. NrmCVec |
    ( IndMet ` u ) e. ( CMet ` ( BaseSet ` u ) ) } $.

  ${
    $d u D $.  $d u U $.  $d u X $.
    iscbn.x $e |- X = ( BaseSet ` U ) $.
    iscbn.8 $e |- D = ( IndMet ` U ) $.
    $( A complex Banach space is a normed complex vector space with a complete
       induced metric.  (Contributed by NM, 5-Dec-2006.)  Use ~ isbn instead.
       (New usage is discouraged.) $)
    iscbn $p |- ( U e. CBan <-> ( U e. NrmCVec /\ D e. ( CMet ` X ) ) ) $=
      ( vu cv cims cfv cba ccmet wcel cnv ccbn wceq fveq2 eqtr4di fveq2d df-cbn
      eleq12d elrab2 ) FGZHIZUBJIZKIZLACKIZLFBMNUBBOZUCAUEUFUGUCBHIAUBBHPEQUGUD
      CKUGUDBJICUBBJPDQRTFSUA $.

    $( The induced metric on complex Banach space is complete.  (Contributed by
       NM, 8-Sep-2007.)  Use ~ bncmet (or preferably ~ bncms ) instead.
       (New usage is discouraged.) $)
    cbncms $p |- ( U e. CBan -> D e. ( CMet ` X ) ) $=
      ( ccbn wcel cnv ccmet cfv iscbn simprbi ) BFGBHGACIJGABCDEKL $.
  $}

  $( Every complex Banach space is a normed complex vector space.  (Contributed
     by NM, 17-Mar-2007.)  Use ~ bnnvc instead.  (New usage is discouraged.) $)
  bnnv $p |- ( U e. CBan -> U e. NrmCVec ) $=
    ( ccbn wcel cnv cims cfv cba ccmet eqid iscbn simplbi ) ABCADCAEFZAGFZHFCLA
    MMILIJK $.

  $( The class of all complex Banach spaces is a relation.  (Contributed by NM,
     17-Mar-2007.)  (New usage is discouraged.) $)
  bnrel $p |- Rel CBan $=
    ( vx ccbn cnv wss wrel cv bnnv ssriv nvrel relss mp2 ) BCDCEBEABCAFGHIBCJK
    $.

  ${
    bnsscmcl.x $e |- X = ( BaseSet ` U ) $.
    bnsscmcl.d $e |- D = ( IndMet ` U ) $.
    bnsscmcl.j $e |- J = ( MetOpen ` D ) $.
    bnsscmcl.h $e |- H = ( SubSp ` U ) $.
    bnsscmcl.y $e |- Y = ( BaseSet ` W ) $.
    $( A subspace of a Banach space is a Banach space iff it is closed in the
       norm-induced metric of the parent space.  (Contributed by NM,
       1-Feb-2008.)  (New usage is discouraged.) $)
    bnsscmcl $p |- ( ( U e. CBan /\ W e. H ) -> ( W e. CBan <->
                Y e. ( Clsd ` J ) ) ) $=
      ( ccbn wcel cfv ccmet cnv wb sylan syl cims cxp cres ccld bnnv sspnv eqid
      wa iscbn baib wceq sspims eleq1d cbncms adantr cmetss 3bitrd ) BMNZECNZUH
      ZEMNZEUAOZGPOZNZAGGUBUCZVCNZGDUDONZUTEQNZVAVDRURBQNZUSVHBUEZBCEKUFSVAVHVD
      VBEGLVBUGZUIUJTUTVBVEVCURVIUSVBVEUKVJVBABCEGLIVKKULSUMUTAFPONZVFVGRURVLUS
      ABFHIUNUOADFGJUPTUQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples of complex Banach spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    cnbn.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The set of complex numbers is a complex Banach space.  (Contributed by
       Steve Rodriguez, 4-Jan-2007.)  (New usage is discouraged.) $)
    cnbn $p |- U e. CBan $=
      ( ccbn wcel cnv caddc cmul cop cabs cims cfv cc ccmet cnnv cmin ccom eqid
      cnims eqcomi cncmet cnnvba fveq2i iscbn mpbir2an ) ACDAEDFGHIHZJKZLMKDABN
      UFIOPZUFUGUEUEQUGQRSTUFALABUAAJKUFAUEJBUBSUCUD $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Uniform Boundedness Theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d c k n r x y z A $.  $d c k n r t x z D $.  $d k n t x y J $.
    $d d k t x z K $.  $d c d k m n r t u x y z N $.  $d t z P $.
    $d c k n r t x y ph $.  $d d t x z R $.  $d c d k m n r t u x y z T $.
    $d c d n r t x y z U $.  $d c d n r t x y W $.  $d c d k m n r t x y z X $.
    ubth.1 $e |- X = ( BaseSet ` U ) $.
    ubth.2 $e |- N = ( normCV ` W ) $.
    ${
      ubthlem.3 $e |- D = ( IndMet ` U ) $.
      ubthlem.4 $e |- J = ( MetOpen ` D ) $.
      ubthlem.5 $e |- U e. CBan $.
      ubthlem.6 $e |- W e. NrmCVec $.
      ubthlem.7 $e |- ( ph -> T C_ ( U BLnOp W ) ) $.
      ${
        ubthlem.8 $e |- ( ph -> A. x e. X E. c e. RR A. t e. T
                                ( N ` ( t ` x ) ) <_ c ) $.
        ubthlem.9 $e |- A = ( k e. NN |-> { z e. X |
                              A. t e. T ( N ` ( t ` z ) ) <_ k } ) $.
        $( Lemma for ~ ubth .  The function ` A ` exhibits a countable
           collection of sets that are closed, being the inverse image under
           ` t ` of the closed ball of radius ` k ` , and by assumption they
           cover ` X ` .  Thus, by the Baire Category theorem ~ bcth2 , for
           some ` n ` the set ` A `` n ` has an interior, meaning that there is
           a closed ball ` { z e. X | ( y D z ) <_ r } ` in the set.
           (Contributed by Mario Carneiro, 11-Jan-2014.)
           (New usage is discouraged.) $)
        ubthlem1 $p |- ( ph -> E. n e. NN E. y e. X E. r e. RR+
                        { z e. X | ( y D z ) <_ r } C_ ( A ` n ) ) $=
          ( cv cfv cnt c0 wne cn wrex co cle wbr crab wss crp ccld wf cuni wceq
          wral wcel wa rzal ralrimivw rabid2 sylibr eqcomd eleq1d iinrab adantl
          crn ciin ccnv cba cima cims cmopn cblo sselda ccn eqid ccbn cnv ax-mp
          id bnnv blocn2 ctopon wb cxmet ccmet cmet cbncms cmetmet metxmet mp2b
          mopntopon imsxmet iscncl mp2an sylib syl adantlr ffvelcdmda biantrurd
          simpld fveq2 breq1d elrab bitr4di pm5.32da 2fveq3 a1i wfn ffn cr cn0v
          cxr nvzcl mp3an12 clt wi simpr syl2an adantr sylancr ralimdva elssuni
          cvv sseld sylan rexlimdva mpd wex sstr2 ex elpreima 3syl eqrdv imaeq2
          3bitr4d simprd nnre ad2antlr nvnd mpan xmetsym eqtr4d rabbiia rspcdva
          rexrd blcld eqeltrd ralrimiva syl2anr eqeltrrd ctop mopntop toponunii
          iincld topcld pm2.61ne fmptd cpw frnd cldss2 sstrdi sspwuni arch ltle
          impr an32s nvcl simpllr simplrl letr syl3anc mpan2d expr fvexi fvmpt2
          rabex mpan2 eleq2d ralbidv bitrdi bicomd sylan9bbr ffnd sylbird syl6d
          fnfvelrn dfss3 eqssd ne0i bcth2 mpanl12 ffvelcdm sselid elpwid ntrss3
          syl2anc cbl ntropn mopni2 mp3an1 sseqtrrdi c2 ntrss2 syl5com ad2antrr
          cdiv w3a jctil rphalfcl rpxrd rpxr rphalflt 3jca breq2 rabbidv sseq1d
          blsscls2 rspcev 3syld syldan jcad eximdv n0 df-rex 3imtr4g reximdva )
          AKUGZFUHZLUIUHUHZUJUKZKULUMZCUGZDUGZGUNZPUGZUOUPZDOUQZUYRURZPUSUMZCOU
          MZKULUMAULLUTUHZFVAZFVOZVBZOVCZVUAAJULVUCEUGZUHMUHZJUGZUOUPZEHVDZDOUQ
          ZVUKFAVURULVEZVFZVVAVUKVEOVUKVEZHUJHUJVCZVVAOVUKVVEOVVAVVEVUTDOVDOVVA
          VCVVEVUTDOVUSEHVGVHVUTDOVIVJVKVLVVCHUJUKZVFEHVUSDOUQZVPZVVAVUKVVFVVHV
          VAVCVVCVUSEDHOVMVNVVFVVFVVGVUKVEZEHVDVVHVUKVEVVCVVFWIVVCVVIEHVVCVUPHV
          EZVFZVVGVUPVQZVUBMUHZVURUOUPZCNVRUHZUQZVSZVUKVVKBVVGVVQVVKBUGZOVEZVVR
          VUPUHZMUHZVURUOUPZVFZVVSVVTVVPVEZVFZVVRVVGVEZVVRVVQVEZVVKVVSVWBVWDVVK
          VVSVFZVWBVVTVVOVEZVWBVFVWDVWHVWIVWBVVKOVVOVVRVUPAVVJOVVOVUPVAZVVBAVVJ
          VFZVWJVVLVVRVSZVUKVEZBNVTUHZWAUHZUTUHZVDZVWKVUPINWBUNZVEZVWJVWQVFZAHV
          WRVUPUDWCVWSVUPLVWOWDUNVEZVWTVWRGVWNVUPILVWONTVWNWEZUAVWOWEZVWRWEIWFV
          EZIWGVEZUBIWJWHZUCWKLOWLUHVEZVWOVVOWLUHVEZVXAVWTWMGOWNUHVEZVXGGOWOUHV
          EZGOWPUHVEVXIVXDVXJUBGIORTWQWHZGOWRGOWSWTZGLOUAXAWHZVWNVVOWNUHVEZVXHN
          WGVEZVXNUCVWNNVVOVVOWEZVXBXBWHZVWNVWOVVOVXCXAWHBVUPLVWOOVVOXCXDXEXFZX
          JZXGZXHXIVVNVWBCVVTVVOVUBVVTVCVVMVWAVURUOVUBVVTMXKXLXMXNXOVWFVWCWMVVK
          VUSVWBDVVROVUCVVRVCZVUQVWAVURUOVUCVVRMVUPXPXLZXMXQVVKVWJVUPOXRVWGVWEW
          MVXTOVVOVUPXSOVVRVVPVUPUUAUUBUUEUUCVVKVWMVVQVUKVEBVWPVVPVVRVVPVCVWLVV
          QVUKVVRVVPVVLUUDVLAVVJVWQVVBVWKVWJVWQVXRUUFXGVVKVURYBVEZVVPVWPVEZVVKV
          URVVBVURXTVEZAVVJVURUUGZUUHUUOVXNNYAUHZVVOVEZVYCVYDVXQVXOVYHUCNVVOVYG
          VXPVYGWEZYCWHZCVWNVYGVURVVPVWOVVOVXCVVNVYGVUBVWNUNZVURUOUPCVVOVUBVVOV
          EZVVMVYKVURUOVYLVVMVUBVYGVWNUNZVYKVXOVYLVVMVYMVCUCVUBVWNNMVVOVYGVXPVY
          ISVXBUUIUUJVXNVYHVYLVYKVYMVCVXQVYJVYGVUBVWNVVOUUKYDUULXLUUMUUPYDXFUUN
          UUQUUREHVVGLUVDUUSUUTVVDVVCLUVAVEZVVDVXIVYNVXLGLOUAUVBWHZLOOLVXMUVCZU
          VEWHXQUVFUFUVGZAVUNOAVUMOUVHZURVUNOURAVUMVUKVYRAULVUKFVYQUVILOVYPUVJZ
          UVKVUMOUVLXEAVVRVUNVEZBOVDZOVUNURAVWAQUGZUOUPZEHVDZQXTUMZBOVDWUAUEAWU
          EVYTBOAVVSVFZWUDVYTQXTWUFWUBXTVEZVFZWUBVURYEUPZJULUMZWUDVYTYFZWUGWUJW
          UFWUBJUVMVNWUHWUIWUKJULWUHVVBVFWUIWUDVWBEHVDZVYTWUHVVBWUIWUDWULYFWUHV
          VBWUIVFZVFZWUCVWBEHWUNVVJVFZWUCWUBVURUOUPZVWBWUNWUPVVJWUHVVBWUIWUPWUH
          WUGVYEWUIWUPYFVVBWUFWUGYGVYFWUBVURUVNYHUVOYIWUOVWAXTVEZWUGVYEWUCWUPVF
          VWBYFWUHVVJWUQWUMWUFVVJWUQWUGWUFVVJVFVXOVWIWUQUCAVVJVVSVWIVWKOVVOVVRV
          UPVXSXHUVPVVTNMVVOVXPSUVQYJXGXGWUFWUGWUMVVJUVRWUOVVBVYEWUHVVBWUIVVJUV
          SVYFXFVWAWUBVURUVTUWAUWBYKUWCWUFVVBWULVYTYFWUGWUFVVBVFWULVVRVURFUHZVE
          ZVYTVVBWUSVVSWULVFZWUFWULVVBWUSVVRVVAVEWUTVVBWURVVAVVRVVBVVAYMVEWURVV
          AVCVUTDOOIVRRUWDUWFJULVVAYMFUFUWEUWGUWHVUTWULDVVROVYAVUSVWBEHVYBUWIXM
          UWJWUFWULWUTWUFVVSWULAVVSYGXIUWKUWLWUFFULXRZVVBWUSVYTYFAWVAVVSAULVUKF
          VYQUWMYIWVAVVBVFZWURVUNVVRWVBWURVUMVEWURVUNURULVURFUWPWURVUMYLXFYNYOU
          WNXGUWOYPYQYPYKYQBOVUNUWQVJUWRVXJOUJUKZVULVUOVFVUAVXKVXEIYAUHZOVEWVCV
          XFIOWVDRWVDWEYCOWVDUWSWTGKLFOUAUWTUXAUXFAUYTVUJKULAUYQULVEZVFZVUBUYSV
          EZCYRVUBOVEZVUIVFZCYRUYTVUJWVFWVGWVICWVFWVGWVHVUIWVFUYSOVUBWVFVYNUYRO
          URZUYSOURZVYOAVULWVEWVJVYQVULWVEVFZUYROWVLVUKVYRUYRVYSULVUKUYQFUXBUXC
          UXDYOZUYRLOVYPUXEYJYNWVFWVGVUIWVFWVGVFVUBVVRGUXGUHUNZUYSURZBUSUMZVUIW
          VFUYSLVEZWVGWVPWVFVYNWVJWVQVYOWVMUYRLOVYPUXHYJZVXIWVQWVGWVPVXLBUYSGVU
          BLOUAUXIUXJYOWVFWVGWVHWVPVUIYFWVFUYSOVUBWVFWVQWVKWVRWVQUYSLVBOUYSLYLV
          YPUXKXFWCWVFWVHVFZWVOVUIBUSWVSVVRUSVEZVFZWVOWVNUYRURZVUDVVRUXLUXPUNZU
          OUPZDOUQZUYRURZVUIWVFWVOWWBYFWVHWVTWVFUYSUYRURZWVOWWBWVFVYNWVJWWGVYOW
          VMUYRLOVYPUXMYJWVNUYSUYRYSUXNUXOWWAWWEWVNURZWWBWWFYFWVSVXIWVHVFWWCYBV
          EZVVRYBVEZWWCVVRYEUPZUXQWWHWVTWVSWVHVXIWVFWVHYGVXLUXRWVTWWIWWJWWKWVTW
          WCVVRUXSZUXTVVRUYAVVRUYBUYCDGVUBWWCWWEVVRLOUAWWEWEUYGYHWWEWVNUYRYSXFW
          WAWWCUSVEZWWFVUIYFWVTWWMWVSWWLVNWWMWWFVUIVUHWWFPWWCUSVUEWWCVCZVUGWWEU
          YRWWNVUFWWDDOVUEWWCVUDUOUYDUYEUYFUYHYTXFUYIYPUYJYQYTUYKUYLCUYSUYMVUIC
          OUYNUYOUYPYQ $.

        ubthlem.10 $e |- ( ph -> K e. NN ) $.
        ubthlem.11 $e |- ( ph -> P e. X ) $.
        ubthlem.12 $e |- ( ph -> R e. RR+ ) $.
        ubthlem.13 $e |- ( ph -> { z e. X | ( P D z ) <_ R } C_ ( A ` K ) ) $.
        $( Lemma for ~ ubth .  Given that there is a closed ball
           ` B ( P , R ) ` in ` A `` K ` , for any ` x e. B ( 0 , 1 ) ` , we
           have ` P + R x. x e. B ( P , R ) ` and ` P e. B ( P , R ) ` , so
           both of these have ` norm ( t ( z ) ) <_ K ` and so ` norm ( t ( x `
           ` ) ) <_ ( norm ( t ( P ) ) + norm ( t ( P + R x. x ) ) ) / R <_ ( `
           ` K + K ) / R ` , which is our desired uniform bound.  (Contributed
           by Mario Carneiro, 11-Jan-2014.)  (New usage is discouraged.) $)
        ubthlem2 $p |- ( ph -> E. d e. RR A. t e. T
                         ( ( U normOpOLD W ) ` t ) <_ d ) $=
          ( caddc co cdiv cr wcel cv cnmoo cfv cle wbr wral wrex nnrpd rpaddcld
          rpdivcld rpred wa cnmcv c1 wi cns cpv wceq oveq2 breq1d eleq1 imbi12d
          crab wss rabss sylib ad2antrr cnv ccbn bnnv ax-mp a1i crp rpcnd simpr
          cc eqid nvscl syl3anc nvgcl rspcdva cmul cnsb cxmet ccmet cmet cbncms
          cmetmet metxmet mp2b xmetsym imsdval nvpncan2 fveq2d 3eqtrd cc0 eqtrd
          rprege0d nvsge0 mulridd eqcomd breq12d nvcl mpan adantl lemul2d wb cn
          1red ralbidv cba 2fveq3 elrab sylancr adantr ccld mopntopon ffvelcdmd
          syl ctopon syl32anc syld ralrimiva syl2anc bitr4d breq2 rabbidv fvexi
          rabex fvmpt eleq2d bitrdi 3imtr3d com12 ad2antlr xmet0 rpge0d eqbrtrd
          rsp sylanbrc sseldd eleqtrd simprd r19.21bi ccnv cima cims cmopn cblo
          wf sselda ccn blocn2 iscncl mp2an simpld nnred le2add syl22anc mpan2d
          imsxmet clno mp3an12 lnosub lnomul 3eqtr3d ffvelcdmda nvmtri eqbrtrrd
          bloln remulcld readdcld letr mpand lemuldiv2d sylibd cxr rpxrd nmoubi
          adantld mpbird brralrspcev ) AMMULUMZHUNUMZUOUPDUQZJOURUMZUSZUWTUTVAZ
          DIVBUXCRUQUTVADIVBRUOVCAUWTAUWSHAMMAMUHVDZUXEVEZUJVFZVGAUXDDIAUXAIUPZ
          VHZUXDBUQZJVIUSZUSZVJUTVAZUXJUXAUSZNUSZUWTUTVAZVKZBPVBZUXIUXQBPUXIUXJ
          PUPZVHZUXMGHUXJJVLUSZUMZJVMUSZUMZPUPZUYDUXAUSZNUSZMUTVAZDIVBZVHZUXPUX
          TGUYDFUMZHUTVAZUYDMEUSZUPZUXMUYJUXTGCUQZFUMZHUTVAZUYOUYMUPZVKZUYLUYNV
          KCPUYDUYOUYDVNZUYQUYLUYRUYNUYTUYPUYKHUTUYOUYDGFVOVPUYOUYDUYMVQVRAUYSC
          PVBZUXHUXSAUYQCPVSZUYMVTVUAUKUYQCPUYMWAWBWCUXTJWDUPZGPUPZUYBPUPZUYEVU
          CUXTJWEUPZVUCUCJWFWGZWHZAVUDUXHUXSUIWCZUXTVUCHWLUPZUXSVUEVUHUXTHAHWIU
          PUXHUXSUJWCZWJZUXIUXSWKZHUXJUYAJPSUYAWMZWNWOZGUYBJUYCPSUYCWMZWPWOZWQU
          XTUYLHUXLWRUMZHVJWRUMZUTVAUXMUXTUYKVURHVUSUTUXTUYKUYBUXKUSZVURUXTUYKU
          YDGFUMZUYDGJWSUSZUMZUXKUSZVUTUXTFPWTUSUPZVUDUYEUYKVVAVNVVEUXTFPXAUSUP
          ZFPXBUSUPVVEVUFVVFUCFJPSUAXCWGFPXDFPXEXFZWHVUIVUQGUYDFPXGWOUXTVUCUYEV
          UDVVAVVDVNVUHVUQVUIUYDGFJVVBUXKPSVVBWMZUXKWMZUAXHWOUXTVVCUYBUXKUXTVUC
          VUDVUEVVCUYBVNVUHVUIVUOGUYBJUYCVVBPSVUPVVHXIWOZXJXKUXTVUCHUOUPXLHUTVA
          VHZUXSVUTVURVNVUHUXTHVUKXNZVUMHUXJUYAJUXKPSVUNVVIXOWOXMUXTVUSHUXTHVUL
          XPXQXRUXTUXLVJHUXSUXLUOUPZUXIVUCUXSVVMVUGUXJJUXKPSVVIXSXTYAUXTYEVUKYB
          UUAAUYNUYJYCUXHUXSAUYNUYDUYOUXAUSNUSZMUTVAZDIVBZCPVSZUPUYJAUYMVVQUYDA
          MYDUPUYMVVQVNUHKMVVNKUQZUTVAZDIVBZCPVSVVQYDEVVRMVNZVVTVVPCPVWAVVSVVOD
          IVVRMVVNUTUUBYFUUCUGVVPCPPJYGSUUDUUEUUFYOZUUGVVPUYICUYDPUYTVVOUYHDIUY
          TVVNUYGMUTUYOUYDNUXAYHVPYFYIUUHWCUUIUXTUYIUXPUYEUXTUYIUYHUXPUXHUYIUYH
          VKAUXSUYIUXHUYHUYHDIUUOUUJUUKUXTUYHHUXOWRUMZUWSUTVAZUXPUXTUYHUYGGUXAU
          SZNUSZULUMZUWSUTVAZVWDUXTUYHVWFMUTVAZVWHUXIVWIUXSAVWIDIAVUDVWIDIVBZAG
          VVQUPVUDVWJVHAGUYMVVQAVUBUYMGUKAVUDGGFUMZHUTVAZGVUBUPUIAVWKXLHUTAVVEV
          UDVWKXLVNVVGUIGFPUULYJAHUJUUMUUNUYQVWLCGPUYOGVNZUYPVWKHUTUYOGGFVOVPYI
          UUPUUQVWBUURVVPVWJCGPVWMVVOVWIDIVWMVVNVWFMUTUYOGNUXAYHVPYFYIWBUUSUUTY
          KUXTUYGUOUPZVWFUOUPZMUOUPZVWPUYHVWIVHVWHVKUXTOWDUPZUYFOYGUSZUPZVWNUDU
          XTPVWRUYDUXAUXIPVWRUXAUVFZUXSUXIVWTUXAUVAUXJUVBLYLUSUPBOUVCUSZUVDUSZY
          LUSVBZUXIUXAJOUVEUMZUPZVWTVXCVHZAIVXDUXAUEUVGZVXEUXALVXBUVHUMUPZVXFVX
          DFVXAUXAJLVXBOUAVXAWMZUBVXBWMZVXDWMZVUGUDUVILPYPUSUPZVXBVWRYPUSUPZVXH
          VXFYCVVEVXLVVGFLPUBYMWGVWQVXAVWRWTUSUPVXMUDVXAOVWRVWRWMZVXIUVQVXAVXBV
          WRVXJYMXFBUXALVXBPVWRUVJUVKWBYOUVLZYKZVUQYNZUYFONVWRVXNTXSYJZUXTVWQVW
          EVWRUPZVWOUDUXTPVWRGUXAVXPVUIYNZVWEONVWRVXNTXSYJZAVWPUXHUXSAMUHUVMWCZ
          VYBUYGVWFMMUVNUVOUVPUXTVWCVWGUTVAZVWHVWDUXTUYFVWEOWSUSZUMZNUSZVWCVWGU
          TUXTVYFHUXNOVLUSZUMZNUSZVWCUXTVYEVYHNUXTVVCUXAUSZUYBUXAUSZVYEVYHUXTVV
          CUYBUXAVVJXJUXTVUCVWQUXAJOUVRUMZUPZUYEVUDVYJVYEVNVUHVWQUXTUDWHZUXIVYM
          UXSUXIVXEVYMVXGVUCVWQVXEVYMVUGUDVXDUXAJVYLOVYLWMZVXKUWFUVSYOYKZVUQVUI
          UYDGUXAJVYLVVBVYDOPSVVHVYDWMZVYOUVTYQUXTVUCVWQVYMVUJUXSVYKVYHVNVUHVYN
          VYPVULVUMHUXJUYAVYGUXAJVYLOPSVUNVYGWMZVYOUWAYQUWBXJUXTVWQVVKUXNVWRUPZ
          VYIVWCVNVYNVVLUXIPVWRUXJUXAVXOUWCZHUXNVYGONVWRVXNVYRTXOWOXMUXTVWQVWSV
          XSVYFVWGUTVAVYNVXQVXTUYFVWEOVYDNVWRVXNVYQTUWDWOUWEUXTVWCUOUPVWGUOUPUW
          SUOUPZVYCVWHVHVWDVKUXTHUXOUXTHVUKVGUXTVWQVYSUXOUOUPUDVYTUXNONVWRVXNTX
          SYJZUWGUXTUYGVWFVXRVYAUWHAWUAUXHUXSAUWSUXFVGWCZVWCVWGUWSUWIWOUWJYRUXT
          UXOUWSHWUBWUCVUKUWKUWLYRUWPYRYSUXIVWTUWTUWMUPZUXDUXRYCVXOAWUDUXHAUWTU
          XGUWNYKBUWTUXAJUXKNUXBOPVWRSVXNVVITUXBWMVUGUDUWOYTUWQYSRDUXCUWTUTUOIU
          WRYT $.
      $}

      $d d ph $.
      $( Lemma for ~ ubth .  Prove the reverse implication, using ~ nmblolbi .
         (Contributed by Mario Carneiro, 11-Jan-2014.)
         (New usage is discouraged.) $)
      ubthlem3 $p |- ( ph ->
                ( A. x e. X E. c e. RR A. t e. T ( N ` ( t ` x ) ) <_ c <->
                  E. d e. RR A. t e. T ( ( U normOpOLD W ) ` t ) <_ d ) ) $=
        ( cle vz vu vy vr vn vm vk cv cfv wbr wral cr wrex cnmoo co wceq fveq2d
        fveq1 breq1d cbvralvw ralbidv bitrid cbvrexvw 2fveq3 rexralbidv wa crab
        breq2 cn cmpt wss crp cblo adantr bilani cbvrabv rabbidv eqtrid cbvmptv
        ubthlem1 wcel ad3antrrr ad2antrr simplrl simplrr simprl simprr ubthlem2
        expr rexlimdva rexlimdvva mpd biimtrrid cnmcv cmul simpr cnv ccbn ax-mp
        ex bnnv eqid nvcl remulcl syl2an cba wf sselda adantlr ad2ant2r mp3an12
        mpan blof syl simplr ffvelcdmd cxr cmnf clt nmoxr simpllr nmogtmnf xrre
        syl22anc ad2antlr syl2anc nmblolbi cc0 nvge0 jca lemul1a syl31anc letrd
        ralimdva brralrspcev syl6an ralrimdva impbid ) ABUHZCUHZUIZHUIZKUHZTUJZ
        CEUKKULUMZBJUKZYTFIUNUOZUIZLUHZTUJZCEUKZLULUMZUUFUAUHZUBUHZUIZHUIZUUITU
        JZUBEUKZLULUMZUAJUKZAUULUUSUUEUABJUUSUUMYTUIZHUIZUUCTUJZCEUKZKULUMUUMYS
        UPZUUEUURUVDLKULUURUVBUUITUJZCEUKUUIUUCUPZUVDUUQUVFUBCEUUNYTUPZUUPUVBUU
        ITUVHUUOUVAHUUMUUNYTURUQUSUTUVGUVFUVCCEUUIUUCUVBTVHVAVBVCUVEUVCUUDKCULE
        UVEUVBUUBUUCTUUMYSHYTVDUSVEVBUTZAUUTUULAUUTVFZUCUHZUUMDUOUDUHZTUJUAJVGU
        EUHZUFVIUUIUUNUIZHUIZUFUHZTUJZUBEUKZLJVGZVJZUIVKZUDVLUMZUCJUMUEVIUMUULU
        VJBUCUACUVTDEFUGUEGHIJUDKMNOPQRAEFIVMUOZVKZUUTSVNUUTUUFAUVIVOZUFUGVIUVS
        UVBUGUHZTUJZCEUKZUAJVGZUVPUWFUPZUVSUVBUVPTUJZCEUKZUAJVGUWIUVRUWLLUAJUVR
        UUIYTUIZHUIZUVPTUJZCEUKUUIUUMUPZUWLUVQUWOUBCEUVHUVOUWNUVPTUVHUVNUWMHUUI
        UUNYTURUQUSUTUWPUWOUWKCEUWPUWNUVBUVPTUUIUUMHYTVDUSVAVBVPUWJUWLUWHUAJUWJ
        UWKUWGCEUVPUWFUVBTVHVAVQVRVSZVTUVJUWBUULUEUCVIJUVJUVMVIWAZUVKJWAZVFZVFZ
        UWAUULUDVLUXAUVLVLWAZUWAUULUXAUXBUWAVFZVFBUACUVTDUVKUVLEFUGGUVMHIJKLMNO
        PQRAUWDUUTUWTUXCSWBUVJUUFUWTUXCUWEWCUWQUVJUWRUWSUXCWDUVJUWRUWSUXCWEUXAU
        XBUWAWFUXAUXBUWAWGWHWIWJWKWLWTWMAUUKUUFLULAUUIULWAZVFZUUKUUEBJUXEYSJWAZ
        VFZUUIYSFWNUIZUIZWOUOZULWAZUUKUUBUXJTUJZCEUKUUEUXEUXDUXIULWAZUXKUXFAUXD
        WPFWQWAZUXFUXMFWRWAUXNQFXAWSZYSFUXHJMUXHXBZXCXLZUUIUXIXDXEZUXGUUJUXLCEU
        XGYTEWAZUUJUXLUXGUXSUUJVFZVFZUUBUUHUXIWOUOZUXJUYAUUAIXFUIZWAZUUBULWAZUY
        AJUYCYSYTUYAYTUWCWAZJUYCYTXGZUXEUXSUYFUXFUUJAUXSUYFUXDAEUWCYTSXHXIXJZUX
        NIWQWAZUYFUYGUXORUWCYTFIJUYCMUYCXBZUWCXBZXMXKXNZUXEUXFUXTXOZXPUYIUYDUYE
        RUUAIHUYCUYJNXCXLXNUYAUUHULWAZUXMUYBULWAUYAUUHXQWAZUXDXRUUHXSUJZUUJUYNU
        YAUYGUYOUYLUXNUYIUYGUYOUXORYTFUUGIJUYCMUYJUUGXBZXTXKXNAUXDUXFUXTYAZUYAU
        YGUYPUYLUXNUYIUYGUYPUXORYTFUUGIJUYCMUYJUYQYBXKXNUXGUXSUUJWGZUUHUUIYCYDZ
        UXFUXMUXEUXTUXQYEUUHUXIXDYFUXGUXKUXTUXRVNUYAUYFUXFUUBUYBTUJUYHUYMYSUWCY
        TFUXHHUUGIJMUXPNUYQUYKUXORYGYFUYAUYNUXDUXMYHUXITUJZVFZUUJUYBUXJTUJUYTUY
        RUXFVUBUXEUXTUXFUXMVUAUXQUXNUXFVUAUXOYSFUXHJMUXPYIXLYJYEUYSUUHUUIUXIYKY
        LYMWIYNKCUUBUXJTULEYOYPYQWJYR $.
    $}

    ubth.3 $e |- M = ( U normOpOLD W ) $.
    $( Uniform Boundedness Theorem, also called the Banach-Steinhaus Theorem.
       Let ` T ` be a collection of bounded linear operators on a Banach space.
       If, for every vector ` x ` , the norms of the operators' values are
       bounded, then the operators' norms are also bounded.  Theorem 4.7-3 of
       [Kreyszig] p. 249.  See also
       ~ http://en.wikipedia.org/wiki/Uniform_boundedness_principle .
       (Contributed by NM, 7-Nov-2007.)  (Proof shortened by Mario Carneiro,
       11-Jan-2014.)  (New usage is discouraged.) $)
    ubth $p |- ( ( U e. CBan /\ W e. NrmCVec /\ T C_ ( U BLnOp W ) ) ->
                 ( A. x e. X E. c e. RR A. t e. T ( N ` ( t ` x ) ) <_ c <->
                   E. d e. RR A. t e. T ( M ` t ) <_ d ) ) $=
      ( cblo co cfv cle wbr wral cr ccbn wcel cnv wss cv wrex wb caddc cmul cop
      wi cabs cif cba cnmoo cnmcv wceq oveq1 sseq2d fveq2 eqtrid raleqdv fveq1d
      breq1d rexralbidv bibi12d imbi12d oveq2 ralbidv cims cmopn elimel elimnvu
      eqid cnbn id ubthlem3 dedth2h 3impia ) DUAUBZGUCUBZCDGNOZUDZAUEBUEZPZFPZI
      UEZQRZBCSITUFZAHSZWDEPZJUEZQRZBCSJTUFZUGZVTWAWCWOUKCVTDUHUIUJULUJZUMZGNOZ
      UDZWIAWQUNPZSZWDWQGUOOZPZWLQRZBCSJTUFZUGZUKCWQWAGWPUMZNOZUDZWEXGUPPZPZWGQ
      RZBCSITUFZAWTSZWDWQXGUOOZPZWLQRZBCSJTUFZUGZUKDGWPWPDWQUQZWCWSWOXFXTWBWRCD
      WQGNURUSXTWJXAWNXEXTWIAHWTXTHDUNPWTKDWQUNUTVAVBXTWMXDJBTCXTWKXCWLQXTWDEXB
      XTEDGUOOXBMDWQGUOURVAVCVDVEVFVGGXGUQZWSXIXFXSYAWRXHCGXGWQNVHUSYAXAXNXEXRY
      AWIXMAWTYAWHXLIBTCYAWFXKWGQYAWEFXJYAFGUPPXJLGXGUPUTVAVCVDVEVIYAXDXQJBTCYA
      XCXPWLQYAWDXBXOGXGWQUOVHVCVDVEVFVGXIABWQVJPZCWQYBVKPZXJXGWTIJWTVNXJVNYBVN
      YCVNDWPUAWPWPVNVOVLGVMXIVPVQVRVS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Minimizing Vector Theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d j n x y F $.  $d k n w x y J $.  $d y K $.  $d y L $.  $d f j w x y M $.
    $d f j w x y N $.  $d f j k n w x y ph $.  $d w x R $.  $d f k n w x y S $.
    $d f j k n w x y A $.  $d f j k n w x y D $.  $d w x y U $.  $d w x y W $.
    $d n T $.  $d j k n w x X $.  $d f j k n w x y Y $.
    minveco.x $e |- X = ( BaseSet ` U ) $.
    minveco.m $e |- M = ( -v ` U ) $.
    minveco.n $e |- N = ( normCV ` U ) $.
    minveco.y $e |- Y = ( BaseSet ` W ) $.
    minveco.u $e |- ( ph -> U e. CPreHilOLD ) $.
    minveco.w $e |- ( ph -> W e. ( ( SubSp ` U ) i^i CBan ) ) $.
    minveco.a $e |- ( ph -> A e. X ) $.
    ${
      minveco.d $e |- D = ( IndMet ` U ) $.
      minveco.j $e |- J = ( MetOpen ` D ) $.
      minveco.r $e |- R = ran ( y e. Y |-> ( N ` ( A M y ) ) ) $.
      $( Lemma for ~ minveco .  The set of all distances from points of ` Y `
         to ` A ` are a nonempty set of nonnegative reals.  (Contributed by
         Mario Carneiro, 8-May-2014.)  (New usage is discouraged.) $)
      minvecolem1 $p |- ( ph ->
                         ( R C_ RR /\ R =/= (/) /\ A. w e. R 0 <_ w ) ) $=
        ( cr wss c0 wne cc0 cv cle wbr wral co cfv cmpt crn wcel wa ccphlo phnv
        cnv syl adantr css ccbn cin elin sylib simpld eqid sspba syl2anc sselda
        nvmcl syl3anc nvcl fmpttd frnd eqsstrid cdm cn0v simprd bnnv nvzcl 3syl
        fvex dmmpti eleqtrrdi ne0d wceq dm0rn0 eqeq1i necon3bii nvge0 ralrimiva
        bitr4i cvv wb rgenw breq2 ralrnmptw ax-mp sylibr raleqi 3jca ) AFUDUEFU
        FUGZUHCUIZUJUKZCFULZAFBMDBUIZIUMZJUNZUOZUPZUDUCAMUDXMABMXLUDAXJMUQZURZG
        VAUQZXKLUQZXLUDUQAXQXOAGUSUQXQRGUTVBZVCZXPXQDLUQZXJLUQXRXTAYAXOTVCAMLXJ
        AXQKGVDUNZUQZMLUEXSAYCKVEUQZAKYBVEVFUQYCYDURSKYBVEVGVHZVIGYBKLMNQYBVJVK
        VLVMDXJGILNOVNVOZXKGJLNPVPVLVQVRVSAXMVTZUFUGXFAYGKWAUNZAYHMYGAYDKVAUQYH
        MUQAYCYDYEWBKWCKMYHQYHVJWDWEBMXLXMXKJWFZXMVJZWGWHWIYGUFFUFYGUFWJXNUFWJF
        UFWJXMWKFXNUFUCWLWPWMVHAXHCXNULZXIAUHXLUJUKZBMULZYKAYLBMXPXQXRYLXTYFXKG
        JLNPWNVLWOXLWQUQZBMULYKYMWRYNBMYIWSXHYLBCMXLXMWQYJXGXLUHUJWTXAXBXCXHCFX
        NUCXDXCXE $.

      minveco.s $e |- S = inf ( R , RR , < ) $.
      ${
        minvecolem2.1 $e |- ( ph -> B e. RR ) $.
        minvecolem2.2 $e |- ( ph -> 0 <_ B ) $.
        minvecolem2.3 $e |- ( ph -> K e. Y ) $.
        minvecolem2.4 $e |- ( ph -> L e. Y ) $.
        minvecolem2.5 $e |- ( ph -> ( ( A D K ) ^ 2 ) <_ ( ( S ^ 2 ) + B ) ) $.
        minvecolem2.6 $e |- ( ph -> ( ( A D L ) ^ 2 ) <_ ( ( S ^ 2 ) + B ) ) $.
        $( Lemma for ~ minveco .  Any two points ` K ` and ` L ` in ` Y ` are
           close to each other if they are close to the infimum of distance to
           ` A ` .  (Contributed by Mario Carneiro, 9-May-2014.)  (Revised by
           AV, 4-Oct-2020.)  (New usage is discouraged.) $)
        minvecolem2 $p |- ( ph -> ( ( K D L ) ^ 2 ) <_ ( 4 x. B ) ) $=
          ( vx vw co c2 cexp c4 cmul cle wbr caddc c1 cdiv cpv cfv cns wcel 4re
          cr clt cinf wss c0 wne cv wral wrex cc0 minvecolem1 simp1d simp2d 0re
          simp3d breq1 ralbidv sylancr infrecl syl3anc eqeltrid resqcld remulcl
          wceq rspcev cmet cnv ccphlo phnv syl imsmet css ccbn cin inss1 sselid
          eqid sspba syl2anc sseldd metcl readdcld ax-1cn halfcl syl22anc nvgcl
          cc mp1i eqeltrrd nvmcl wb mpbird fveq2d wa pm3.2i lemul2 mp3an3 mpbid
          a1i recnd 2re 2cn oveq1i eqtrdi eqtr3d oveq12d oveq1d imsdval 3eqtr4d
          syl13anc sspgval sspnv sspsval nvcl infregelb syl31anc breqtrrdi cmpt
          nvscl oveq2 rspceeqv sylancl fvex elrnmpti eleqtrrdi infrelb eqbrtrid
          crn sylibr le2sq2 4pos leadd1dd le2addd 2timesd breqtrrd phpar2 sqmul
          2pos sq2 cabs nvs 0le2 absid mp2an nvmdi 2thalfe1 nvsid eqtrid nvsass
          nv2 nvaddsub4 syl122anc 3eqtr2d metsym nvnnncan1 oveq2d 2t2e4 mulassd
          eqtr3id 3brtr4d letrd 4cn adddid breqtrd leadd2d ) AJKEUPZUQURUPZUSDU
          TUPZVAVBUSGUQURUPZUTUPZUWQVCUPZUWTUWRVCUPZVAVBAUXAUSUWSDVCUPZUTUPZUXB
          VAAUXAUSCVDUQVEUPZJKHVFVGZUPZHVHVGZUPZLUPZMVGZUQURUPZUTUPZUWQVCUPZUXD
          AUWTUWQAUSVKVIZUWSVKVIZUWTVKVIVJAGAGFVKVLVMZVKUGAFVKVNZFVOVPZUNVQZUOV
          QZVAVBZUOFVRZUNVKVSZUXQVKVIAUXRUXSVTUYAVAVBZUOFVRZABUOCEFHILMNOPQRSTU
          AUBUCUDUEUFWAZWBZAUXRUXSUYFUYGWCZAVTVKVIZUYFUYDWDAUXRUXSUYFUYGWEZUYCU
          YFUNVTVKUXTVTWNUYBUYEUOFUXTVTUYAVAWFWGWOWHZUNUOFWIWJWKZWLZUSUWSWMWHZA
          UWPAEOWPVGVIZJOVIZKOVIZUWPVKVIAHWQVIZUYPAHWRVIZUYSUAHWSWTZEHOQUDXAWTZ
          APOJAUYSNHXBVGZVIZPOVNVUAAVUCXCXDVUCNVUCXCXEUBXFZHVUCNOPQTVUCXGZXHXIZ
          UJXJZAPOKVUGUKXJZJKEOXKWJWLZXLAUXMUWQAUXOUXLVKVIZUXMVKVIVJAUXKAUYSUXJ
          OVIZUXKVKVIZVUAAUYSCOVIZUXIOVIZVULVUAUCAPOUXIVUGAUXEUXGNVHVGZUPZUXIPA
          UYSVUDUXEXQVIZUXGPVIZVUQUXIWNVUAVUEVDXQVIVURAXMVDXNXRZAJKNVFVGZUPZUXG
          PAUYSVUDJPVIZKPVIZVVBUXGWNVUAVUEUJUKJKHVVAUXFVUCNPTUXFXGZVVAXGZVUFUUA
          XOANWQVIZVVCVVDVVBPVIAUYSVUDVVGVUAVUEHVUCNVUFUUBXIZUJUKJKNVVAPTVVFXPW
          JXSZUXEUXGVUPUXHHVUCNPTUXHXGZVUPXGZVUFUUCXOAVVGVURVUSVUQPVIVVHVUTVVIU
          XEUXGVUPNPTVVKUUIWJXSZXJZCUXIHLOQRXTWJZUXJHMOQSUUDXIZWLZUSUXLWMWHZVUJ
          XLAUXOUXCVKVIZUXDVKVIVJAUWSDUYNUHXLZUSUXCWMWHAUWTUXMUWQUYOVVQVUJAUWSU
          XLVAVBZUWTUXMVAVBZAGVKVIVTGVAVBVUMGUXKVAVBVVTUYMAVTUXQGVAAVTUXQVAVBZU
          YFUYKAUXRUXSUYDUYJVWBUYFYAUYHUYIUYLUYJAWDYIUNUOUOFVTUUEUUFYBUGUUGVVOA
          GUXQUXKVAUGAUXRUYDUXKFVIUXQUXKVAVBUYHUYLAUXKBPCBVQZLUPZMVGZUUHZUURZFA
          UXKVWEWNBPVSZUXKVWGVIAUXIPVIUXKUXKWNVWHVVLUXKXGBUXIPVWEUXKUXKVWCUXIWN
          VWDUXJMVWCUXICLUUJYCUUKUULBPVWEUXKVWFVWFXGVWDMUUMUUNUUSUFUUOUNUOUXKFU
          UPWJUUQGUXKUUTXOAUXPVUKVVTVWAYAZUYNVVPUXPVUKUXOVTUSVLVBZYDVWIUXOVWJVJ
          UVAYEUWSUXLUSYFYGXIYHUVBAUQCJEUPZUQURUPZCKEUPZUQURUPZVCUPZUTUPZUQUQUX
          CUTUPZUTUPZUXNUXDVAAVWOVWQVAVBZVWPVWRVAVBZAVWOUXCUXCVCUPVWQVAAVWLVWNU
          XCUXCAVWKAUYPVUNUYQVWKVKVIVUBUCVUHCJEOXKWJWLZAVWMAUYPVUNUYRVWMVKVIVUB
          UCVUICKEOXKWJWLZVVSVVSULUMUVCAUXCAUXCVVSYJZUVDUVEAVWOVKVIZVWQVKVIZVWS
          VWTYAZAVWLVWNVXAVXBXLAUQVKVIZVVRVXEYKVVSUQUXCWMWHVXDVXEVXGVTUQVLVBZYD
          VXFVXGVXHYKUVHYEVWOVWQUQYFYGXIYHACJLUPZCKLUPZUXFUPZMVGZUQURUPZVXIVXJL
          UPZMVGZUQURUPZVCUPZUQVXIMVGZUQURUPZVXJMVGZUQURUPZVCUPZUTUPZUXNVWPAUYT
          VXIOVIZVXJOVIZVXQVYCWNUAAUYSVUNUYQVYDVUAUCVUHCJHLOQRXTWJAUYSVUNUYRVYE
          VUAUCVUICKHLOQRXTWJVXIVXJHUXFLMOQVVERSUVFWJAUXMVXMUWQVXPVCAUQUXKUTUPZ
          UQURUPZUXMVXMAVYGUQUQURUPZUXLUTUPZUXMAUQXQVIZUXKXQVIVYGVYIWNYLAUXKVVO
          YJUQUXKUVGWHVYHUSUXLUTUVIYMYNAVYFVXLUQURAUQUXJUXHUPZMVGZVYFVXLAVYLUQU
          VJVGZUXKUTUPZVYFAUYSVYJVULVYLVYNWNVUAVYJAYLYIZVVNUQUXJUXHHMOQVVJSUVKW
          JVYMUQUXKUTVXGVTUQVAVBVYMUQWNYKUVLUQUVMUVNYMYNAVYKVXKMAVYKUQCUXHUPZUQ
          UXIUXHUPZLUPZCCUXFUPZUXGLUPZVXKAUYSVYJVUNVUOVYKVYRWNVUAVYOUCVVMUQCUXI
          UXHHLOQRVVJUVOYTAVYSVYPUXGVYQLAUYSVUNVYSVYPWNVUAUCCUXHHUXFOQVVEVVJUVT
          XIAUQUXEUTUPZUXGUXHUPZUXGVYQAWUBVDUXGUXHUPZUXGWUAVDUXGUXHUVPYMAUYSUXG
          OVIZWUCUXGWNVUAAUYSUYQUYRWUDVUAVUHVUIJKHUXFOQVVEXPWJZUXGUXHHOQVVJUVQX
          IUVRAUYSVYJVURWUDWUBVYQWNVUAVYOVUTWUEUQUXEUXGUXHHOQVVJUVSYTYOYPAUYSVU
          NVUNUYQUYRVYTVXKWNVUAUCUCVUHVUICCJKHUXFLOQVVERUWAUWBUWCYCYOYQYOAUWPVX
          OUQURAKJEUPZKJLUPZMVGZUWPVXOAUYSUYRUYQWUFWUHWNVUAVUIVUHKJEHLMOQRSUDYR
          WJAUYPUYQUYRUWPWUFWNVUBVUHVUIJKEOUWDWJAVXNWUGMAUYSVUNUYQUYRVXNWUGWNVU
          AUCVUHVUICJKHLOQRUWEYTYCYSYQYPAVWOVYBUQUTAVWLVXSVWNVYAVCAVWKVXRUQURAU
          YSVUNUYQVWKVXRWNVUAUCVUHCJEHLMOQRSUDYRWJYQAVWMVXTUQURAUYSVUNUYRVWMVXT
          WNVUAUCVUICKEHLMOQRSUDYRWJYQYPUWFYSAUXDUQUQUTUPZUXCUTUPVWRWUIUSUXCUTU
          WGYMAUQUQUXCVYOVYOVXCUWHUWIUWJUWKAUSUWSDUSXQVIAUWLYIAUWSUYNYJADUHYJUW
          MUWNAUWQUWRUWTVUJAUXODVKVIUWRVKVIVJUHUSDWMWHUYOUWOYB $.
      $}

      ${
        minveco.f $e |- ( ph -> F : NN --> Y ) $.
        minveco.1 $e |- ( ( ph /\ n e. NN ) ->
            ( ( A D ( F ` n ) ) ^ 2 ) <_ ( ( S ^ 2 ) + ( 1 / n ) ) ) $.
        $( Lemma for ~ minveco .  The sequence formed by taking elements
           successively closer to the infimum is Cauchy.  (Contributed by Mario
           Carneiro, 8-May-2014.)  (Revised by AV, 4-Oct-2020.)
           (New usage is discouraged.) $)
        minvecolem3 $p |- ( ph -> F e. ( Cau ` D ) ) $=
          ( vj vx vw ccau cfv wcel cv co clt wbr cuz wral cn wrex wa c4 c2 cexp
          crp cdiv cfl c1 caddc cr cc0 cle cn0 4re 4pos elrpii cz simpr rpexpcl
          sylancl rpdivcl sylancr rprege0 flge0nn0 nn0p1nn 4syl cmul ccphlo cnv
          cmet phnv imsmet 3syl ad2antrr wss css syl ccbn cin inss1 sselid eqid
          2z sspba syl2anc adantr ffvelcdmd sseldd eluznn sylan syl3anc resqcld
          wf metcl nnrpd rpreccld rpmulcl rpred rpge0d ffvelcdmda syldan oveq2d
          wceq fveq2 oveq1d oveq2 breq12d ralrimiva rspcdva wne rspcev readdcld
          w3a wb cc rpcnne0 mpbird eqidd cinf c0 minvecolem1 breq1 ralbidv mpan
          3anim3i infrecl eqeltrid nnrecred adantlr eluzle adantl rpregt0d nnre
          0re nngt0 lerec mpbid leadd2dd letrd minvecolem2 ax-mp recdiv eqbrtrd
          flltp1 ltrec1d pm3.2i ltmuldiv2 mp3an3 metge0 ad2antlr lt2sq syl21anc
          jca lelttrd breq1d raleqbidv nnuz cxmet imsxmet 1zzd fssd iscauf ) AI
          DULUMUNUIUOZIUMZHUOZIUMZDUPZUJUOZUQURZHUWEUSUMZUTZUIVAVBZUJVGUTAUWNUJ
          VGAUWJVGUNZVCZVDUWJVEVFUPZVHUPZVIUMZVJVKUPZVAUNZUWTIUMZUWHDUPZUWJUQUR
          ZHUWTUSUMZUTZUWNUWPUWRVGUNZUWRVLUNZVMUWRVNURVCUWSVOUNUXAUWPVDVGUNZUWQ
          VGUNZUXGVDVPVQVRZUWPUWOVEVSUNUXJAUWOVTXEUWJVEWAWBZVDUWQWCWDZUWRWEUWRW
          FUWSWGWHZUWPUXDHUXEUWPUWGUXEUNZVCZUXDUXCVEVFUPZUWQUQURZUXPUXQVDVJUWTV
          HUPZWIUPZUWQUXPUXCUXPDNWLUMUNZUXBNUNZUWHNUNZUXCVLUNZAUYAUWOUXOAGWJUNZ
          GWKUNZUYATGWMZDGNPUCWNWOWPZUXPONUXBAONWQZUWOUXOAUYFMGWRUMZUNUYIAUYEUY
          FTUYGWSAUYJWTXAZUYJMUYJWTXBUAXCGUYJMNOPSUYJXDXFXGZWPZUXPVAOUWTIAVAOIX
          OZUWOUXOUGWPZUWPUXAUXOUXNXHZXIZXJZUXPONUWHUYMUXPVAOUWGIUYOUWPUXAUXOUW
          GVAUNZUXNUWGUWTXKXLZXIXJZUXBUWHDNXPXMZXNUXPUXTUXPUXIUXSVGUNZUXTVGUNUX
          KUXPUWTUXPUWTUYPXQZXRVDUXSXSWDXTUXPUWQUWPUXJUXOUXLXHZXTZUXPBCUXSDEFGJ
          UXBUWHKLMNOPQRSAUYEUWOUXOTWPAMUYKUNUWOUXOUAWPACNUNZUWOUXOUBWPZUCUDUEU
          FUXPUXSUWPVUCUXOUWPUWTUWPUWTUXNXQXRXHZXTZUXPUXSVUIYAUYQUWPUXOUYSUWHOU
          NUYTUWPVAOUWGIAUYNUWOUGXHYBYCZUXPCUWHDUPZVEVFUPZFVEVFUPZVJUWGVHUPZVKU
          PZVNURZCUXBDUPZVEVFUPZVUNUXSVKUPZVNURHVAUWTUWGUWTYEZVUMVUSVUPVUTVNVVA
          VULVURVEVFVVAUWHUXBCDUWGUWTIYFYDYGVVAVUOUXSVUNVKUWGUWTVJVHYHYDYIAVUQH
          VAUTUWOUXOAVUQHVAUHYJWPUYPYKUXPVUMVUPVUTUXPVULUXPUYAVUGUYCVULVLUNUYHV
          UHUXPONUWHUYMVUKXJCUWHDNXPXMXNUXPVUNVUOAVUNVLUNUWOUXOAFAFEVLUQUUAZVLU
          FAEVLWQZEUUBYLZVMUKUOZVNURZUKEUTZYOVVCVVDUWJVVEVNURZUKEUTZUJVLVBZYOVV
          BVLUNABUKCDEGJKLMNOPQRSTUAUBUCUDUEUUCVVGVVJVVCVVDVMVLUNVVGVVJUUPVVIVV
          GUJVMVLUWJVMYEVVHVVFUKEUWJVMVVEVNUUDUUEYMUUFUUGUJUKEUUHWOUUIXNWPZUXPU
          WGUYTUUJZYNUXPVUNUXSVVKVUJYNUWPUXOUYSVUQUYTAUYSVUQUWOUHUUKYCUXPVUOUXS
          VUNVVLVUJVVKUXPUWTUWGVNURZVUOUXSVNURZUXOVVMUWPUWTUWGUULUUMUXPUWTVLUNV
          MUWTUQURVCUWGVLUNZVMUWGUQURZVCZVVMVVNYPUXPUWTVUDUUNUXPUYSVVQUYTUYSVVO
          VVPUWGUUOUWGUUQUVOWSUWTUWGUURXGUUSUUTUVAUVBUXPUXTUWQUQURZUXSUWQVDVHUP
          ZUQURZUXPVVSUWTUXPUXJUXIVVSVGUNVUEUXKUWQVDWCWBVUDUXPVJVVSVHUPZUWRUWTU
          QUXPUWQYQUNUWQVMYLVCZVDYQUNVDVMYLVCZVWAUWRYEUXPUXJVWBVUEUWQYRWSUXIVWC
          UXKVDYRUVCUWQVDUVDWBUXPUXHUWRUWTUQURUXPUWRUWPUXGUXOUXMXHXTUWRUVFWSUVE
          UVGUXPUXSVLUNZUWQVLUNZVVRVVTYPZVUJVUFVWDVWEVDVLUNZVMVDUQURZVCVWFVWGVW
          HVPVQUVHUXSUWQVDUVIUVJXGYSUVPUXPUYDVMUXCVNURZUWJVLUNVMUWJVNURVCZUXDUX
          RYPVUBUXPUYAUYBUYCVWIUYHUYRVUAUXBUWHDNUVKXMUWOVWJAUXOUWJWEUVLUXCUWJUV
          MUVNYSYJUWMUXFUIUWTVAUWEUWTYEZUWKUXDHUWLUXEUWEUWTUSYFVWKUWIUXCUWJUQVW
          KUWFUXBUWHDUWEUWTIYFYGUVQUVRYMXGYJAUJUWHUWFDUIHIVJNVAUVSAUYEUYFDNUVTU
          MUNTUYGDGNPUCUWAWOAUWBAUYSVCUWHYTAUWEVAUNVCUWFYTAVAONIUGUYLUWCUWDYS
          $.

        $( Lemma for ~ minveco . ` F ` is convergent in the subspace topology
           on ` Y ` .  (Contributed by Mario Carneiro, 7-May-2014.)
           (New usage is discouraged.) $)
        minvecolem4a $p |- ( ph -> F
                      ( ~~>t ` ( MetOpen ` ( D |` ( Y X. Y ) ) ) )
                      ( ( ~~>t ` ( MetOpen ` ( D |` ( Y X. Y ) ) ) ) ` F ) ) $=
          ( cxp cres cmopn cfv clm cdm wcel wbr cba ccmet ccau cims wceq ccphlo
          cnv css phnv syl ccbn wa elin sylib simpld eqid sspims syl2anc simprd
          cin cbncms eqeltrrd minvecolem3 cxmet cn wf wb cmet imsmet 3syl causs
          metxmet mpbid cmetcau cha wfun xmetres methaus lmfun funfvbrb ) AIDOO
          UIUJZUKULZUMULZUNUOZIIWSULWSUPZAWQMUQULZURULZUOIWQUSULUOZWTAMUTULZWQX
          CAGVCUOZMGVDULZUOZXEWQVAAGVBUOZXFTGVEZVFAXHMVGUOZAMXGVGVPUOXHXKVHUAMX
          GVGVIVJZVKXEDGXGMOSUCXEVLZXGVLVMVNAXKXEXCUOAXHXKXLVOXEMXBXBVLXMVQVFVR
          AIDUSULUOZXDABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHVSADNVTULUOZWAOIWBXNX
          DWCADNWDULUOZXOAXIXFXPTXJDGNPUCWEWFDNWHVFZUGDINOWGVNWIWQIWRXBWRVLZWJV
          NAWRWKUOZWSWLWTXAWCAXOWQNOVPZVTULUOXSXQDONWMWQWRXTXRWNWFWRWOIWSWPWFWI
          $.

        $( Lemma for ~ minveco .  The convergent point of the Cauchy sequence
           ` F ` is a member of the base space.  (Contributed by Mario
           Carneiro, 16-Jun-2014.)  (New usage is discouraged.) $)
        minvecolem4b $p |- ( ph -> ( ( ~~>t ` J ) ` F ) e. X ) $=
          ( clm cfv cnv wcel css wss ccphlo phnv syl ccbn cin elin sylib simpld
          eqid sspba syl2anc cxp cres cmopn wfun wbr wceq cxmet imsxmet methaus
          wa cha lmfun minvecolem4a crest co c1 cvv nnuz cba fvexi ctop mopntop
          cn a1i ctopon xmetres2 mopntopon lmcl 1zzd metrest fveq2d breqd bitrd
          lmss mpbird funbrfv sylc eqeltrd sseldd ) AONIJUIUJZUJZAGUKULZMGUMUJZ
          ULZONUNZAGUOULXGTGUPUQZAXIMURULZAMXHURUSULXIXLVOUAMXHURUTVAVBGXHMNOPS
          XHVCVDVEZAXFIDOOVFVGZVHUJZUIUJZUJZOAXEVIZIXQXEVJZXFXQVKAJVPULZXRADNVL
          UJULZXTAXGYAXKDGNPUCVMUQZDJNUDVNUQJVQUQAXSIXQXPVJZABCDEFGHIJKLMNOPQRS
          TUAUBUCUDUEUFUGUHVRZAXSIXQJOVSVTZUIUJZVJYCAXQIJYEWAWBOWHYEVCWCOWBULAO
          MWDSWEWIAYAJWFULYBDJNUDWGUQAXOOWJUJULZYCXQOULAXNOVLUJULZYGAYAXJYHYBXM
          DONWKVEXNXOOXOVCZWLUQYDXQIXOOWMVEZAWNUGWSAYFXPIXQAYEXOUIAYAXJYEXOVKYB
          XMDXNJXONOXNVCUDYIWOVEWPWQWRWTIXQXEXAXBYJXCXD $.

        $( Lemma for ~ minveco .  The infimum of the distances to ` A ` is a
           real number.  (Contributed by Mario Carneiro, 16-Jun-2014.)
           (Revised by AV, 4-Oct-2020.)  (New usage is discouraged.) $)
        minvecolem4c $p |- ( ph -> S e. RR ) $=
          ( vx vw cr clt cinf wss c0 wne cle wbr wral wrex wcel cc0 minvecolem1
          cv simp1d simp2d 0re simp3d wceq breq1 ralbidv rspcev sylancr infrecl
          syl3anc eqeltrid ) AFEUKULUMZUKUFAEUKUNZEUOUPZUIVDZUJVDZUQURZUJEUSZUI
          UKUTZVQUKVAAVRVSVBWAUQURZUJEUSZABUJCDEGJKLMNOPQRSTUAUBUCUDUEVCZVEAVRV
          SWFWGVFAVBUKVAWFWDVGAVRVSWFWGVHWCWFUIVBUKVTVBVIWBWEUJEVTVBWAUQVJVKVLV
          MUIUJEVNVOVP $.

        minveco.t $e |- T = ( 1 /
      ( ( ( ( ( A D ( ( ~~>t ` J ) ` F ) ) + S ) / 2 ) ^ 2 ) - ( S ^ 2 ) ) ) $.
        $( Lemma for ~ minveco .  The convergent point of the Cauchy sequence
           ` F ` attains the minimum distance, and so is closer to ` A ` than
           any other point in ` Y ` .  (Contributed by Mario Carneiro,
           7-May-2014.)  (Revised by AV, 4-Oct-2020.)
           (New usage is discouraged.) $)
        minvecolem4 $p |- ( ph -> E. x e. Y A. y e. Y
                          ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) $=
          ( vw clm cfv wcel co cle wbr wral wrex cxp cres cmopn wfun wceq cxmet
          cha ccphlo cnv phnv imsxmet 3syl methaus lmfun minvecolem4a crest cvv
          cv c1 cn eqid nnuz cba fvexi a1i ctop syl mopntop ctopon wss css ccbn
          cin elin sylib simpld sspba syl2anc xmetres2 mopntopon lmcl 1zzd lmss
          metrest fveq2d breqd mpbird funbrfv sylc eqeltrd minvecolem4b imsdval
          wa bitrd syl3anc adantr cr cmet metcl clt caddc c2 cdiv cexp readdcld
          cc0 crp resqcld recnd 2timesd breq1d wb 3bitr2d ralbidv rspcev metge0
          cmul 0re ad2antrr letrd imsmet minvecolem4c sselda nvcl wn ltnled cfl
          nvmcl cuz cn0 cmin rehalfcld resubcld ltadd1d 2re 2pos ltmuldiv2 cinf
          pm3.2i c0 wne minvecolem1 simp3d simp1d simp2d breq1 sylancr syl31anc
          infregelb breqtrrdi addge0d divge0 lt2sqd posdifd 3bitrd biimpa elrpd
          syl21anc rpreccld eqeltrid rprege0d flge0nn0 nnzd rexrd simpll eluznn
          nn0p1nn breqtrrd sylan fssd ffvelcdmda nnrecred rpred reflcl peano2re
          nnred fllep1 eluzle adantl eqbrtrrid 1red nngt0d syl122anc leaddsub2d
          lediv23 mpbid le2sqd lmle leadd2d lemuldiv2 mp3an3 biimpar ex sylbird
          syldan pm2.18d cmpt crn simpr fvex elrnmpt1 sylancl eleqtrrdi infrelb
          eqbrtrid eqbrtrrd ralrimiva oveq2 ) AKLUMUNZUNZQUODUYJMUPZNUNZDCVRZMU
          PZNUNZUQURZCQUSZDBVRZMUPZNUNZUYOUQURZCQUSZBQUTAUYJKEQQVAVBZVCUNZUMUNZ
          UNZQAUYIVDZKVUFUYIURZUYJVUFVEAEPVFUNUOZLVGUOVUGAIVHUOZIVIUOZVUIUBIVJZ
          EIPRUEVKZVLZELPUFVMLVNVLAVUHKVUFVUEURZACDEFGIJKLMNOPQRSTUAUBUCUDUEUFU
          GUHUIUJVOZAVUHKVUFLQVPUPZUMUNZURVUOAVUFKLVUQVSVQQVTVUQWAWBQVQUOAQOWCU
          AWDWEAVUKVUILWFUOAVUJVUKUBVULWGZVUMELPUFWHVLAVUDQWIUNUOZVUOVUFQUOAVUC
          QVFUNUOZVUTAVUIQPWJZVVAVUNAVUKOIWKUNZUOZVVBVUSAVVDOWLUOZAOVVCWLWMUOVV
          DVVEXMUCOVVCWLWNWOWPIVVCOPQRUAVVCWAWQWRZEQPWSWRVUCVUDQVUDWAZWTWGVUPVU
          FKVUDQXAWRZAXBUIXCAVURVUEKVUFAVUQVUDUMAVUIVVBVUQVUDVEVUNVVFEVUCLVUDPQ
          VUCWAUFVVGXDWRXEXFXNXGZKVUFUYIXHXIZVVHXJAUYPCQAUYMQUOZXMZDUYJEUPZUYLU
          YOUQAVVMUYLVEZVVKAVUKDPUOZUYJPUOZVVNVUSUDACDEFGIJKLMNOPQRSTUAUBUCUDUE
          UFUGUHUIUJXKZDUYJEIMNPRSTUEXLXOXPVVLVVMGUYOAVVMXQUOZVVKAEPXRUNUOZVVOV
          VPVVRAVUJVUKVVSUBVULEIPRUEUUAVLZUDVVQDUYJEPXSXOZXPAGXQUOZVVKACDEFGIJK
          LMNOPQRSTUAUBUCUDUEUFUGUHUIUJUUBZXPVVLVUKUYNPUOZUYOXQUOAVUKVVKVUSXPZV
          VLVUKVVOUYMPUOVWDVWEAVVOVVKUDXPAQPUYMVVFUUCDUYMIMPRSUUHXOUYNINPRTUUDW
          RAVVMGUQURZVVKAVWFAVWFUUEGVVMXTURZVWFAGVVMVWCVWAUUFAVWGVWFAVWGVVMVVMG
          YAUPZYBYCUPZUQURZVWFAVWGXMZEUYJDVWIJKLHUUGUNZVSYAUPZPVWMUUIUNZVWNWAUF
          AVUIVWGVUNXPVWKVWMVWKHXQUOZYFHUQURXMVWLUUJUOVWMVTUOZVWKHVWKHVSVWIYBYD
          UPZGYBYDUPZUUKUPZYCUPZYGUKVWKVWSVWKVWSAVWSXQUOZVWGAVWQVWRAVWIAVWHAVVM
          GVWAVWCYEZUULZYHZAGVWCYHZUUMZXPAVWGYFVWSXTURZAVWGGVWIXTURZVWRVWQXTURV
          XGAVWGGGYAUPZVWHXTURYBGYQUPZVWHXTURZVXHAGVVMGVWCVWAVWCUUNAVXJVXIVWHXT
          AGAGVWCYIYJYKAVWBVWHXQUOZYBXQUOZYFYBXTURZXMZVXKVXHYLVWCVXBVXOAVXMVXNU
          UOUUPUUSZWEZGVWHYBUUQXOYMAGVWIVWCVXCAYFFXQXTUURZGUQAYFVXRUQURZYFULVRZ
          UQURZULFUSZAFXQWJZFUUTUVAZVYBACULDEFILMNOPQRSTUAUBUCUDUEUFUGUVBZUVCZA
          VYCVYDUYRVXTUQURZULFUSZBXQUTZYFXQUOZVXSVYBYLAVYCVYDVYBVYEUVDZAVYCVYDV
          YBVYEUVEAVYJVYBVYIYRVYFVYHVYBBYFXQUYRYFVEVYGVYAULFUYRYFVXTUQUVFYNYOUV
          GZVYJAYRWEBULULFYFUVIUVHXGUHUVJZAVXLYFVWHUQURVXOYFVWIUQURZVXBAVVMGVWA
          VWCAVVSVVOVVPYFVVMUQURVVTUDVVQDUYJEPYPXOVYMUVKVXQVWHYBUVLUVRZUVMAVWRV
          WQVXEVXDUVNUVOUVPZUVQUVSUVTZUWAHUWBVWLUWGVLZUWCAKUYJUYIURVWGAKVUFUYJU
          YIVVIVVJUWHXPAVVOVWGUDXPVWKVWIAVWIXQUOZVWGVXCXPUWDVWKJVRZVWNUOZXMZDVY
          TKUNZEUPZVWIUQURWUDYBYDUPZVWQUQURWUBWUEVWRVSVYTYCUPZYAUPZVWQWUBWUDWUB
          AVYTVTUOZWUDXQUOZAVWGWUAUWEZVWKVWPWUAWUHVYRVYTVWMUWFUWIZAWUHXMZVVSVVO
          WUCPUOZWUIAVVSWUHVVTXPZAVVOWUHUDXPZAVTPVYTKAVTQPKUIVVFUWJUWKZDWUCEPXS
          XOWRZYHWUBVWRWUFWUBGAVWBVWGWUAVWCYSYHZWUBVYTWUKUWLZYEAVWQXQUOVWGWUAVX
          DYSZWUBAWUHWUEWUGUQURWUJWUKUJWRWUBWUGVWQUQURWUFVWSUQURZWUBVWTVYTUQURZ
          WVAWUBVWTHVYTUQUKWUBHVWMVYTWUBHVWKHYGUOWUAVYQXPUWMZWUBVWOVWLXQUOVWMXQ
          UOWVCHUWNVWLUWOVLWUBVYTWUKUWPZWUBVWOHVWMUQURWVCHUWQWGWUAVWMVYTUQURVWK
          VWMVYTUWRUWSYTUWTWUBVSXQUOVXAVXGVYTXQUOYFVYTXTURWVBWVAYLWUBUXAAVXAVWG
          WUAVXFYSVWKVXGWUAVYPXPWVDWUBVYTWUKUXBVSVWSVYTUXEUXCUXFWUBVWRWUFVWQWUR
          WUSWUTUXDXGYTWUBWUDVWIWUQAVYSVWGWUAVXCYSWUBAWUHYFWUDUQURZWUJWUKWULVVS
          VVOWUMWVEWUNWUOWUPDWUCEPYPXOWRAVYNVWGWUAVYOYSUXGXGUXHAVWFVWJAVWFVVMVV
          MYAUPZVWHUQURYBVVMYQUPZVWHUQURZVWJAVVMGVVMVWAVWCVWAUXIAWVGWVFVWHUQAVV
          MAVVMVWAYIYJYKAVVRVXLWVHVWJYLZVWAVXBVVRVXLVXOWVIVXPVVMVWHYBUXJUXKWRYM
          UXLUXOUXMUXNUXPXPVVLGVXRUYOUQUHVVLVYCVYIUYOFUOVXRUYOUQURAVYCVVKVYKXPA
          VYIVVKVYLXPVVLUYOCQUYOUXQZUXRZFVVLVVKUYOVQUOUYOWVKUOAVVKUXSUYNNUXTCQU
          YOWVJVQWVJWAUYAUYBUGUYCBULUYOFUYDXOUYEYTUYFUYGVUBUYQBUYJQUYRUYJVEZVUA
          UYPCQWVLUYTUYLUYOUQWVLUYSUYKNUYRUYJDMUYHXEYKYNYOWR $.
      $}

      $( Lemma for ~ minveco .  Discharge the assumption about the sequence
         ` F ` by applying countable choice ~ ax-cc .  (Contributed by Mario
         Carneiro, 9-May-2014.)  (Revised by AV, 4-Oct-2020.)
         (New usage is discouraged.) $)
      minvecolem5 $p |- ( ph -> E. x e. Y A. y e. Y
                        ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) $=
        ( vf vn vw vk cn cv wf cfv co c2 cexp c1 cdiv caddc cle wbr wral wa wex
        wrex wcel csqrt wn clt cc0 nnrecgt0 adantl nnrecre cinf wss minvecolem1
        cr c0 wne w3a adantr simp1d simp2d 0re simp3d wceq breq1 ralbidv rspcev
        sylancr infrecl syl3anc eqeltrid resqcld ltaddposd mpbid readdcld elrpd
        sqge0d addgegt0d resqrtth syl2anc breqtrrd rpsqrtcld rpred wb infregelb
        rpge0d 0red syl31anc mpbird breqtrrdi sqrtge0d lt2sqd ltnled breq2i crn
        bitrid cmpt raleqi fvex rgenw breq2 ralrnmptw ax-mp bitri bitrdi rexnal
        cvv eqid mtbid sylibr cnv syl ad2antrr ccbn breq1d oveq1d oveq2 oveq2d
        ccphlo phnv css cin inss1 sselid sspba sselda nvmcl letrid nvge0 le2sqd
        nvcl ord bitrd notbid imsdval 3imtr4d reximdva mpd ralrimiva cba nnenom
        fvexi axcc4 clm cmin simprl simprr fveq2 breq12d rspccva sylan exlimddv
        minvecolem4 ) AUJNUFUKZULZDUGUKZUVPUMZEUNZUOUPUNZGUOUPUNZUQUVRURUNZUSUN
        ZUTVAZUGUJVBZVCZDBUKZJUNKUMDCUKZJUNZKUMZUTVACNVBBNVEUFADUWIEUNZUOUPUNZU
        WDUTVAZCNVEZUGUJVBUWGUFVDAUWOUGUJAUVRUJVFZVCZUWDVGUMZUWKUTVAZVHZCNVEZUW
        OUWQUWSCNVBZVHUXAUWQUWRGUTVAZUXBUWQGUWRVIVAZUXCVHUWQUXDUWBUWRUOUPUNZVIV
        AUWQUWBUWDUXEVIUWQVJUWCVIVAZUWBUWDVIVAUWPUXFAUVRVKVLZUWQUWCUWBUWPUWCVQV
        FAUVRVMVLZUWQGUWQGFVQVIVNZVQUEUWQFVQVOZFVRVSZUWHUHUKZUTVAZUHFVBZBVQVEZU
        XIVQVFUWQUXJUXKVJUXLUTVAZUHFVBZAUXJUXKUXQVTUWPACUHDEFHIJKLMNOPQRSTUAUBU
        CUDVPWAZWBZUWQUXJUXKUXQUXRWCZUWQVJVQVFZUXQUXOWDUWQUXJUXKUXQUXRWEZUXNUXQ
        BVJVQUWHVJWFUXMUXPUHFUWHVJUXLUTWGWHWIWJZBUHFWKWLWMZWNZWOWPUWQUWDVQVFZVJ
        UWDUTVAUXEUWDWFZUWQUWBUWCUYEUXHWQZUWQUWDUWQUWDUYHUWQUWBUWCUYEUXHUWQGUYD
        WSUXGWTWRZXHZUWDXAXBZXCUWQGUWRUYDUWQUWRUWQUWDUYIXDXEZUWQVJUXIGUTUWQVJUX
        IUTVAZUXQUYBUWQUXJUXKUXOUYAUYMUXQXFUXSUXTUYCUWQXIBUHUHFVJXGXJXKUEXLUWQU
        WDUYHUYJXMZXNXKUWQGUWRUYDUYLXOWPUWQUXCUWRUXLUTVAZUHFVBZUXBUXCUWRUXIUTVA
        ZUWQUYPGUXIUWRUTUEXPUWQUXJUXKUXOUWRVQVFZUYQUYPXFUXSUXTUYCUYLBUHUHFUWRXG
        XJXRUYPUYOUHCNUWKXSZXQZVBZUXBUYOUHFUYTUDXTUWKYIVFZCNVBVUAUXBXFVUBCNUWJK
        YAYBUYOUWSCUHNUWKUYSYIUYSYJUXLUWKUWRUTYCYDYEYFYGYKUWSCNYHYLUWQUWTUWNCNU
        WQUWINVFZVCZUWDUWKUOUPUNZUTVAZVHVUEUWDUTVAZUWTUWNVUDVUFVUGVUDUWDVUEUWQU
        YFVUCUYHWAVUDUWKVUDHYMVFZUWJMVFZUWKVQVFAVUHUWPVUCAHUUAVFZVUHSHUUBYNZYOZ
        VUDVUHDMVFZUWIMVFZVUIVULAVUMUWPVUCUAYOZUWQNMUWIANMVOZUWPAVUHLHUUCUMZVFV
        UPVUKAVUQYPUUDZVUQLVUQYPUUETUUFHVUQLMNORVUQYJUUGXBWAUUHZDUWIHJMOPUUIWLZ
        UWJHKMOQUUMXBZWNUUJUUNVUDUWSVUFVUDUWSUXEVUEUTVAVUFVUDUWRUWKUWQUYRVUCUYL
        WAVVAUWQVJUWRUTVAVUCUYNWAVUDVUHVUIVJUWKUTVAVULVUTUWJHKMOQUUKXBUULVUDUXE
        UWDVUEUTUWQUYGVUCUYKWAYQUUOUUPVUDUWMVUEUWDUTVUDUWLUWKUOUPVUDVUHVUMVUNUW
        LUWKWFVULVUOVUSDUWIEHJKMOPQUBUUQWLYRYQUURUUSUUTUVAUWNUWECNUFUGUJNLUVBRU
        VDUVCUWIUVSWFZUWMUWAUWDUTVVBUWLUVTUOUPUWIUVSDEYSYRYQUVEYNAUWGVCZBCDEFGU
        QDUVPIUVFUMUMEUNGUSUNUOURUNUOUPUNUWBUVGUNURUNZHUIUVPIJKLMNOPQRAVUJUWGSW
        AALVURVFUWGTWAAVUMUWGUAWAUBUCUDUEAUVQUWFUVHVVCUWFUIUKZUJVFDVVEUVPUMZEUN
        ZUOUPUNZUWBUQVVEURUNZUSUNZUTVAZAUVQUWFUVIUWEVVKUGVVEUJUVRVVEWFZUWAVVHUW
        DVVJUTVVLUVTVVGUOUPVVLUVSVVFDEUVRVVEUVPUVJYTYRVVLUWCVVIUWBUSUVRVVEUQURY
        SYTUVKUVLUVMVVDYJUVOUVN $.

      $( Lemma for ~ minveco .  Any minimal point is less than ` S ` away from
         ` A ` .  (Contributed by Mario Carneiro, 9-May-2014.)  (Revised by AV,
         4-Oct-2020.)  (New usage is discouraged.) $)
      minvecolem6 $p |- ( ( ph /\ x e. Y ) ->
        ( ( ( A D x ) ^ 2 ) <_ ( ( S ^ 2 ) + 0 ) <->
          A. y e. Y ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) ) $=
        ( vw cv wcel wa co cexp cc0 caddc cle wbr cfv wral cnv wceq ccphlo phnv
        c2 syl adantr css wss ccbn cin inss1 sselid eqid syl2anc sselda imsdval
        sspba syl3anc oveq1d cr clt cinf wne wrex w3a minvecolem1 simp1d simp2d
        0red simp3d breq1 ralbidv rspcev infrecl eqeltrid resqcld recnd addridd
        c0 breq12d nvmcl nvcl nvge0 wb infregelb mpbird breqtrrdi le2sqd breq2i
        syl31anc bitrid 3bitr2d cmpt crn raleqi cvv rgenw breq2 ralrnmptw ax-mp
        fvex bitri bitrdi ) ABUGZNUHZUIZDYBEUJZVBUKUJZGVBUKUJZULUMUJZUNUOZDYBJU
        JZKUPZUFUGZUNUOZUFFUQZYKDCUGJUJZKUPZUNUOZCNUQZYDYIYKVBUKUJZYGUNUOYKGUNU
        OZYNYDYFYSYHYGUNYDYEYKVBUKYDHURUHZDMUHZYBMUHZYEYKUSAUUAYCAHUTUHUUASHVAV
        CZVDZAUUBYCUAVDZANMYBAUUALHVEUPZUHNMVFUUDAUUGVGVHUUGLUUGVGVITVJHUUGLMNO
        RUUGVKVOVLVMZDYBEHJKMOPQUBVNVPVQYDYGYDYGYDGYDGFVRVSVTZVRUEYDFVRVFZFWQWA
        ZYBYLUNUOZUFFUQZBVRWBZUUIVRUHYDUUJUUKULYLUNUOZUFFUQZAUUJUUKUUPWCYCACUFD
        EFHIJKLMNOPQRSTUAUBUCUDWDVDZWEZYDUUJUUKUUPUUQWFZYDULVRUHZUUPUUNYDWGZYDU
        UJUUKUUPUUQWHZUUMUUPBULVRYBULUSUULUUOUFFYBULYLUNWIWJWKVLZBUFFWLVPWMZWNW
        OWPWRYDYKGYDUUAYJMUHZYKVRUHZUUEYDUUAUUBUUCUVEUUEUUFUUHDYBHJMOPWSVPZYJHK
        MOQWTVLZUVDYDUUAUVEULYKUNUOUUEUVGYJHKMOQXAVLYDULUUIGUNYDULUUIUNUOZUUPUV
        BYDUUJUUKUUNUUTUVIUUPXBUURUUSUVCUVABUFUFFULXCXHXDUEXEXFYTYKUUIUNUOZYDYN
        GUUIYKUNUEXGYDUUJUUKUUNUVFUVJYNXBUURUUSUVCUVHBUFUFFYKXCXHXIXJYNYMUFCNYP
        XKZXLZUQZYRYMUFFUVLUDXMYPXNUHZCNUQUVMYRXBUVNCNYOKXSXOYMYQCUFNYPUVKXNUVK
        VKYLYPYKUNXPXQXRXTYA $.

      $( Lemma for ~ minveco .  Since any two minimal points are distance zero
         away from each other, the minimal point is unique.  (Contributed by
         Mario Carneiro, 9-May-2014.)  (New usage is discouraged.) $)
      minvecolem7 $p |- ( ph -> E! x e. Y A. y e. Y
                        ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) $=
        ( vw cv co cfv cle wbr wral wrex wa wceq wreu minvecolem5 wcel cexp cc0
        wi c2 caddc c4 cmul ccphlo ad2antrr css ccbn cin cr 0re simplrl simplrr
        a1i simprl simprr minvecolem2 ex wb minvecolem6 adantrr adantrl anbi12d
        0le0 4cn mul01i breq2i cmet cnv phnv syl adantr imsmet wss inss1 sselid
        eqid sspba syl2anc sseldd metcl syl3anc sqge0d biantrud resqcld sylancl
        letri3 recnd sqeq0 meteq0 bitrd 3bitr2d bitrid 3imtr3d ralrimivva oveq2
        cc fveq2d breq1d ralbidv reu4 sylanbrc ) ADBUGZJUHZKUIZDCUGJUHKUIZUJUKZ
        CNULZBNUMYIDUFUGZJUHZKUIZYGUJUKZCNULZUNZYDYJUOZVAZUFNULBNULYIBNUPABCDEF
        GHIJKLMNOPQRSTUAUBUCUDUEUQAYQBUFNNAYDNURZYJNURZUNZUNZDYDEUHVBUSUHGVBUSU
        HUTVCUHZUJUKZDYJEUHVBUSUHUUBUJUKZUNZYDYJEUHZVBUSUHZVDUTVEUHZUJUKZYOYPUU
        AUUEUUIUUAUUEUNZCDUTEFGHIYDYJJKLMNOPQRAHVFURZYTUUESVGALHVHUIZVIVJZURYTU
        UETVGADMURYTUUEUAVGUBUCUDUEUTVKURZUUJVLVOUTUTUJUKUUJWEVOAYRYSUUEVMAYRYS
        UUEVNUUAUUCUUDVPUUAUUCUUDVQVRVSUUAUUCYIUUDYNAYRUUCYIVTYSABCDEFGHIJKLMNO
        PQRSTUAUBUCUDUEWAWBAYSUUDYNVTYRAUFCDEFGHIJKLMNOPQRSTUAUBUCUDUEWAWCWDUUI
        UUGUTUJUKZUUAYPUUHUTUUGUJVDWFWGWHUUAUUOUUOUTUUGUJUKZUNZUUGUTUOZYPUUAUUP
        UUOUUAUUFUUAEMWIUIURZYDMURZYJMURZUUFVKURUUAHWJURZUUSAUVBYTAUUKUVBSHWKWL
        ZWMEHMOUBWNWLZUUANMYDANMWOZYTAUVBLUULURUVEUVCAUUMUULLUULVIWPTWQHUULLMNO
        RUULWRWSWTWMZAYRYSVPXAZUUANMYJUVFAYRYSVQXAZYDYJEMXBXCZXDXEUUAUUGVKURUUN
        UURUUQVTUUAUUFUVIXFVLUUGUTXHXGUUAUURUUFUTUOZYPUUAUUFXRURUURUVJVTUUAUUFU
        VIXIUUFXJWLUUAUUSUUTUVAUVJYPVTUVDUVGUVHYDYJEMXKXCXLXMXNXOXPYIYNBUFNYPYH
        YMCNYPYFYLYGUJYPYEYKKYDYJDJXQXSXTYAYBYC $.
    $}

    $( Minimizing vector theorem, or the Hilbert projection theorem.  There is
       exactly one vector in a complete subspace ` W ` that minimizes the
       distance to an arbitrary vector ` A ` in a parent inner product space.
       Theorem 3.3-1 of [Kreyszig] p. 144, specialized to subspaces instead of
       convex subsets.  (Contributed by NM, 11-Apr-2008.)  (Proof shortened by
       Mario Carneiro, 9-May-2014.)  (New usage is discouraged.) $)
    minveco $p |- ( ph -> E! x e. Y A. y e. Y
                   ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) ) $=
      ( vj cfv eqid cims cv co cmpt crn cr cinf cmopn wceq oveq2 fveq2d cbvmptv
      clt rneqi minvecolem7 ) ABCDEUASZRJDRUBZFUCZGSZUDZUEZVAUFUMUGZEUPUHSZFGHI
      JKLMNOPQUPTVCTUTCJDCUBZFUCZGSZUDRCJUSVFUQVDUIURVEGUQVDDFUJUKULUNVBTUO $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Complex Hilbert spaces
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CHilOLD $.

  $( Extend class notation with the class of all complex Hilbert spaces. $)
  chlo $a class CHilOLD $.

  $( Define the class of all complex Hilbert spaces.  A Hilbert space is a
     Banach space which is also an inner product space.  (Contributed by Steve
     Rodriguez, 28-Apr-2007.)  (New usage is discouraged.) $)
  df-hlo $a |- CHilOLD = ( CBan i^i CPreHilOLD ) $.

  $( The predicate "is a complex Hilbert space."  A Hilbert space is a Banach
     space which is also an inner product space, i.e. whose norm satisfies the
     parallelogram law.  (Contributed by Steve Rodriguez, 28-Apr-2007.)
     (New usage is discouraged.) $)
  ishlo $p |- ( U e. CHilOLD <-> ( U e. CBan /\ U e. CPreHilOLD ) ) $=
    ( ccbn ccphlo chlo df-hlo elin2 ) ABCDEF $.

  $( Every complex Hilbert space is a complex Banach space.  (Contributed by
     Steve Rodriguez, 28-Apr-2007.)  (New usage is discouraged.) $)
  hlobn $p |- ( U e. CHilOLD -> U e. CBan ) $=
    ( chlo wcel ccbn ccphlo ishlo simplbi ) ABCADCAECAFG $.

  $( Every complex Hilbert space is an inner product space (also called a
     pre-Hilbert space).  (Contributed by NM, 28-Apr-2007.)
     (New usage is discouraged.) $)
  hlph $p |- ( U e. CHilOLD -> U e. CPreHilOLD ) $=
    ( chlo wcel ccbn ccphlo ishlo simprbi ) ABCADCAECAFG $.

  $( The class of all complex Hilbert spaces is a relation.  (Contributed by
     NM, 17-Mar-2007.)  (New usage is discouraged.) $)
  hlrel $p |- Rel CHilOLD $=
    ( vx chlo ccbn wss wrel cv hlobn ssriv bnrel relss mp2 ) BCDCEBEABCAFGHIBCJ
    K $.

  $( Every complex Hilbert space is a normed complex vector space.
     (Contributed by NM, 17-Mar-2007.)  (New usage is discouraged.) $)
  hlnv $p |- ( U e. CHilOLD -> U e. NrmCVec ) $=
    ( chlo wcel ccbn cnv hlobn bnnv syl ) ABCADCAECAFAGH $.

  ${
    hlnvi.1 $e |- U e. CHilOLD $.
    $( Every complex Hilbert space is a normed complex vector space.
       (Contributed by NM, 6-Jun-2008.)  (New usage is discouraged.) $)
    hlnvi $p |- U e. NrmCVec $=
      ( chlo wcel cnv hlnv ax-mp ) ACDAEDBAFG $.
  $}

  ${
    hlvc.1 $e |- W = ( 1st ` U ) $.
    $( Every complex Hilbert space is a complex vector space.  (Contributed by
       NM, 7-Sep-2007.)  (New usage is discouraged.) $)
    hlvc $p |- ( U e. CHilOLD -> W e. CVecOLD ) $=
      ( chlo wcel cnv cvc hlnv nvvc syl ) ADEAFEBGEAHABCIJ $.
  $}

  ${
    hlcmet.x $e |- X = ( BaseSet ` U ) $.
    hlcmet.8 $e |- D = ( IndMet ` U ) $.
    $( The induced metric on a complex Hilbert space is complete.  (Contributed
       by NM, 8-Sep-2007.)  (New usage is discouraged.) $)
    hlcmet $p |- ( U e. CHilOLD -> D e. ( CMet ` X ) ) $=
      ( chlo wcel ccbn ccmet cfv hlobn cbncms syl ) BFGBHGACIJGBKABCDELM $.

    $( The induced metric on a complex Hilbert space.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlmet $p |- ( U e. CHilOLD -> D e. ( Met ` X ) ) $=
      ( chlo wcel ccmet cfv cmet hlcmet cmetmet syl ) BFGACHIGACJIGABCDEKACLM
      $.
  $}

  ${
    hlpar2.1 $e |- X = ( BaseSet ` U ) $.
    hlpar2.2 $e |- G = ( +v ` U ) $.
    hlpar2.3 $e |- M = ( -v ` U ) $.
    hlpar2.6 $e |- N = ( normCV ` U ) $.
    $( The parallelogram law satisfied by Hilbert space vectors.  (Contributed
       by Steve Rodriguez, 28-Apr-2007.)  (New usage is discouraged.) $)
    hlpar2 $p |- ( ( U e. CHilOLD /\ A e. X /\ B e. X ) ->
      ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A M B ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) ) $=
      ( chlo wcel ccphlo co cfv c2 cexp caddc cmul wceq hlph phpar2 syl3an1 ) C
      LMCNMAGMBGMABDOFPQROABEOFPQROSOQAFPQROBFPQROSOTOUACUBABCDEFGHIJKUCUD $.
  $}

  ${
    hlpar.1 $e |- X = ( BaseSet ` U ) $.
    hlpar.2 $e |- G = ( +v ` U ) $.
    hlpar.4 $e |- S = ( .sOLD ` U ) $.
    hlpar.6 $e |- N = ( normCV ` U ) $.
    $( The parallelogram law satisfied by Hilbert space vectors.  (Contributed
       by Steve Rodriguez, 28-Apr-2007.)  (New usage is discouraged.) $)
    hlpar $p |- ( ( U e. CHilOLD /\ A e. X /\ B e. X ) ->
      ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A G ( -u 1 S B ) ) ) ^ 2 ) ) =
        ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) ) $=
      ( chlo wcel ccphlo co cfv c2 cexp c1 caddc cneg cmul wceq phpar syl3an1
      hlph ) DLMDNMAGMBGMABEOFPQROASUABCOEOFPQROTOQAFPQROBFPQROTOUBOUCDUFABCDEF
      GHIJKUDUE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Standard axioms for a complex Hilbert space
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    hlex.1 $e |- X = ( BaseSet ` U ) $.
    $( The base set of a Hilbert space is a set.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlex $p |- X e. _V $=
      ( cba fvexi ) BADCE $.
  $}

  ${
    hladdf.1 $e |- X = ( BaseSet ` U ) $.
    hladdf.2 $e |- G = ( +v ` U ) $.
    $( Mapping for Hilbert space vector addition.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hladdf $p |- ( U e. CHilOLD -> G : ( X X. X ) --> X ) $=
      ( chlo wcel cnv cxp wf hlnv nvgf syl ) AFGAHGCCICBJAKABCDELM $.

    $( Hilbert space vector addition is commutative.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlcom $p |- ( ( U e. CHilOLD /\ A e. X /\ B e. X ) ->
                ( A G B ) = ( B G A ) ) $=
      ( chlo wcel cnv co wceq hlnv nvcom syl3an1 ) CHICJIAEIBEIABDKBADKLCMABCDE
      FGNO $.

    $( Hilbert space vector addition is associative.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlass $p |- ( ( U e. CHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                   ( ( A G B ) G C ) = ( A G ( B G C ) ) ) $=
      ( chlo wcel cnv w3a co wceq hlnv nvass sylan ) DIJDKJAFJBFJCFJLABEMCEMABC
      EMEMNDOABCDEFGHPQ $.
  $}

  ${
    hl0cl.1 $e |- X = ( BaseSet ` U ) $.
    hl0cl.5 $e |- Z = ( 0vec ` U ) $.
    $( The Hilbert space zero vector.  (Contributed by NM, 7-Sep-2007.)
       (New usage is discouraged.) $)
    hl0cl $p |- ( U e. CHilOLD -> Z e. X ) $=
      ( chlo wcel cnv hlnv nvzcl syl ) AFGAHGCBGAIABCDEJK $.
  $}

  ${
    hladdid.1 $e |- X = ( BaseSet ` U ) $.
    hladdid.2 $e |- G = ( +v ` U ) $.
    hladdid.5 $e |- Z = ( 0vec ` U ) $.
    $( Hilbert space addition with the zero vector.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hladdid $p |- ( ( U e. CHilOLD /\ A e. X ) -> ( A G Z ) = A ) $=
      ( chlo wcel cnv co wceq hlnv nv0rid sylan ) BIJBKJADJAECLAMBNABCDEFGHOP
      $.
  $}

  ${
    hlmulf.1 $e |- X = ( BaseSet ` U ) $.
    hlmulf.4 $e |- S = ( .sOLD ` U ) $.
    $( Mapping for Hilbert space scalar multiplication.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlmulf $p |- ( U e. CHilOLD -> S : ( CC X. X ) --> X ) $=
      ( chlo wcel cnv cc cxp wf hlnv nvsf syl ) BFGBHGICJCAKBLABCDEMN $.

    $( Hilbert space scalar multiplication by one.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlmulid $p |- ( ( U e. CHilOLD /\ A e. X ) -> ( 1 S A ) = A ) $=
      ( chlo wcel cnv c1 co wceq hlnv nvsid sylan ) CGHCIHADHJABKALCMABCDEFNO
      $.

    $( Hilbert space scalar multiplication associative law.  (Contributed by
       NM, 7-Sep-2007.)  (New usage is discouraged.) $)
    hlmulass $p |- ( ( U e. CHilOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
                   ( ( A x. B ) S C ) = ( A S ( B S C ) ) ) $=
      ( chlo wcel cnv cc w3a cmul co wceq hlnv nvsass sylan ) EIJEKJALJBLJCFJMA
      BNOCDOABCDODOPEQABCDEFGHRS $.
  $}

  ${
    hldi.1 $e |- X = ( BaseSet ` U ) $.
    hldi.2 $e |- G = ( +v ` U ) $.
    hldi.4 $e |- S = ( .sOLD ` U ) $.
    $( Hilbert space scalar multiplication distributive law.  (Contributed by
       NM, 7-Sep-2007.)  (New usage is discouraged.) $)
    hldi $p |- ( ( U e. CHilOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
                  ( A S ( B G C ) ) = ( ( A S B ) G ( A S C ) ) ) $=
      ( chlo wcel cnv cc w3a co wceq hlnv nvdi sylan ) EKLEMLANLBGLCGLOABCFPDPA
      BDPACDPFPQERABCDEFGHIJST $.

    $( Hilbert space scalar multiplication distributive law.  (Contributed by
       NM, 7-Sep-2007.)  (New usage is discouraged.) $)
    hldir $p |- ( ( U e. CHilOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) ->
                  ( ( A + B ) S C ) = ( ( A S C ) G ( B S C ) ) ) $=
      ( chlo wcel cnv cc w3a caddc co wceq hlnv nvdir sylan ) EKLEMLANLBNLCGLOA
      BPQCDQACDQBCDQFQRESABCDEFGHIJTUA $.
  $}

  ${
    hlmul0.1 $e |- X = ( BaseSet ` U ) $.
    hlmul0.4 $e |- S = ( .sOLD ` U ) $.
    hlmul0.5 $e |- Z = ( 0vec ` U ) $.
    $( Hilbert space scalar multiplication by zero.  (Contributed by NM,
       7-Sep-2007.)  (New usage is discouraged.) $)
    hlmul0 $p |- ( ( U e. CHilOLD /\ A e. X ) -> ( 0 S A ) = Z ) $=
      ( chlo wcel cnv cc0 co wceq hlnv nv0 sylan ) CIJCKJADJLABMENCOABCDEFGHPQ
      $.
  $}

  ${
    hlipf.1 $e |- X = ( BaseSet ` U ) $.
    hlipf.7 $e |- P = ( .iOLD ` U ) $.
    $( Mapping for Hilbert space inner product.  (Contributed by NM,
       19-Nov-2007.)  (New usage is discouraged.) $)
    hlipf $p |- ( U e. CHilOLD -> P : ( X X. X ) --> CC ) $=
      ( chlo wcel cnv cxp cc wf hlnv ipf syl ) BFGBHGCCIJAKBLABCDEMN $.

    $( Conjugate law for Hilbert space inner product.  (Contributed by NM,
       8-Sep-2007.)  (New usage is discouraged.) $)
    hlipcj $p |- ( ( U e. CHilOLD /\ A e. X /\ B e. X ) ->
                  ( A P B ) = ( * ` ( B P A ) ) ) $=
      ( chlo wcel w3a co ccj cfv wceq cnv hlnv dipcj syl3an1 3com23 eqcomd ) DH
      IZAEIZBEIZJBACKLMZABCKZUAUCUBUDUENZUADOIUCUBUFDPBACDEFGQRST $.
  $}

  ${
    hlipdir.1 $e |- X = ( BaseSet ` U ) $.
    hlipdir.2 $e |- G = ( +v ` U ) $.
    hlipdir.7 $e |- P = ( .iOLD ` U ) $.
    $( Distributive law for Hilbert space inner product.  (Contributed by NM,
       8-Sep-2007.)  (New usage is discouraged.) $)
    hlipdir $p |- ( ( U e. CHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                  ( ( A G B ) P C ) = ( ( A P C ) + ( B P C ) ) ) $=
      ( chlo wcel ccphlo w3a co caddc wceq hlph dipdir sylan ) EKLEMLAGLBGLCGLN
      ABFOCDOACDOBCDOPOQERABCDEFGHIJST $.
  $}

  ${
    hlipass.1 $e |- X = ( BaseSet ` U ) $.
    hlipass.4 $e |- S = ( .sOLD ` U ) $.
    hlipass.7 $e |- P = ( .iOLD ` U ) $.
    $( Associative law for Hilbert space inner product.  (Contributed by NM,
       8-Sep-2007.)  (New usage is discouraged.) $)
    hlipass $p |- ( ( U e. CHilOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) ->
                  ( ( A S B ) P C ) = ( A x. ( B P C ) ) ) $=
      ( chlo wcel ccphlo cc w3a co cmul wceq hlph dipass sylan ) FKLFMLANLBGLCG
      LOABEPCDPABCDPQPRFSABCDEFGHIJTUA $.
  $}

  ${
    hlipgt0.1 $e |- X = ( BaseSet ` U ) $.
    hlipgt0.5 $e |- Z = ( 0vec ` U ) $.
    hlipgt0.7 $e |- P = ( .iOLD ` U ) $.
    $( The inner product of a Hilbert space vector by itself is positive.
       (Contributed by NM, 8-Sep-2007.)  (New usage is discouraged.) $)
    hlipgt0 $p |- ( ( U e. CHilOLD /\ A e. X /\ A =/= Z ) -> 0 < ( A P A ) ) $=
      ( chlo wcel cnv wne cc0 co clt wbr hlnv cfv 3adant3 wceq cnmcv c2 cexp cr
      w3a eqid nvcl wa nvz biimpd necon3d 3impia sqgt0d ipidsq breqtrrd syl3an1
      ) CIJCKJZADJZAELZMAABNZOPCQUQURUSUEZMACUARZRZUBUCNZUTOVAVCUQURVCUDJUSACVB
      DFVBUFZUGSUQURUSVCMLUQURUHZVCMAEVFVCMTAETACVBDEFGVEUIUJUKULUMUQURUTVDTUSA
      BCVBDFVEHUNSUOUP $.
  $}

  ${
    hlcompl.1 $e |- D = ( IndMet ` U ) $.
    hlcompl.2 $e |- J = ( MetOpen ` D ) $.
    $( Completeness of a Hilbert space.  (Contributed by NM, 8-Sep-2007.)
       (Revised by Mario Carneiro, 9-May-2014.)  (New usage is discouraged.) $)
    hlcompl $p |- ( ( U e. CHilOLD /\ F e. ( Cau ` D ) ) ->
                    F e. dom ( ~~>t ` J ) ) $=
      ( chlo wcel cba cfv ccmet ccau clm cdm eqid hlcmet cmetcau sylan ) BGHABI
      JZKJHCALJHCDMJNHABSSOEPACDSFQR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples of complex Hilbert spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    cnhl.6 $e |- U = <. <. + , x. >. , abs >. $.
    $( The set of complex numbers is a complex Hilbert space.  (Contributed by
       Steve Rodriguez, 28-Apr-2007.)  (New usage is discouraged.) $)
    cnchl $p |- U e. CHilOLD $=
      ( chlo wcel ccbn ccphlo cnbn cncph ishlo mpbir2an ) ACDAEDAFDABGABHAIJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Hellinger-Toeplitz Theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d w y F $.  $d w x y z K $.  $d w x y z N $.  $d w z P $.  $d w x y z W $.
    $d w x y z ph $.  $d u v w x y z T $.  $d u v w x y z U $.  $d w x y z X $.
    htth.1 $e |- X = ( BaseSet ` U ) $.
    htth.2 $e |- P = ( .iOLD ` U ) $.
    htth.3 $e |- L = ( U LnOp U ) $.
    htth.4 $e |- B = ( U BLnOp U ) $.
    ${
      htthlem.5 $e |- N = ( normCV ` U ) $.
      htthlem.6 $e |- U e. CHilOLD $.
      htthlem.7 $e |- W = <. <. + , x. >. , abs >. $.
      htthlem.8 $e |- ( ph -> T e. L ) $.
      htthlem.9 $e |- ( ph -> A. x e. X A. y e. X
                        ( x P ( T ` y ) ) = ( ( T ` x ) P y ) ) $.
      htthlem.10 $e |- F = ( z e. X |-> ( w e. X |-> ( w P ( T ` z ) ) ) ) $.
      htthlem.11 $e |- K = ( F " { z e. X | ( N ` z ) <_ 1 } ) $.
      $( Lemma for ~ htth .  The collection ` K ` , which consists of functions
         ` F ( z ) ( w ) = <. w | T ( z ) >. = <. T ( w ) | z >. ` for each
         ` z ` in the unit ball, is a collection of bounded linear functions by
         ~ ipblnfi , so by the Uniform Boundedness theorem ~ ubth , there is a
         uniform bound ` y ` on ` || F ( x ) || ` for all ` x ` in the unit
         ball.  Then ` | T ( x ) | ^ 2 = <. T ( x ) | T ( x ) >. = F ( x ) ( `
         ` T ( x ) ) <_ y | T ( x ) | ` , so ` | T ( x ) | <_ y ` and ` T ` is
         bounded.  (Contributed by NM, 11-Jan-2008.)  (Revised by Mario
         Carneiro, 23-Aug-2014.)  (New usage is discouraged.) $)
      htthlem $p |- ( ph -> T e. B ) $=
        ( wcel cnmoo co cfv cpnf clt wbr cr cv c1 cle wi wral wrex wa cnv hlnvi
        cabs lnof mp3an12 ffvelcdmda nvcl sylancr wceq crab wfun cima cblo cmpt
        wf syl chlo ccphlo hlph ax-mp eqid ipblnfi fmptd ffund eleqtrdi fvelima
        adantr id syl2an ex weq fveq2 breq1d elrab cba oveq2d mpteq2dv mptfvmpt
        fveq1d oveq1 ovex fvmpt sylan9eqr ad2ant2lr rsp2 impl eqtrd fveq2d cmul
        adantrr simpl dipcl mp3an1 abscld mpan ad2antrl remulcld sii 1red nvge0
        cc0 jca simprr lemul2a syl31anc recnd mulridd breqtrd eqbrtrd syl5ibcom
        cc letrd syld syl2anc wb mpbid ad2ant2r mpd expr sylan2b fveq1 ralrimiv
        rexlimdva brralrspcev ralrimiva wss crn imassrn eqsstri frnd ccbn hlobn
        sstrid cnnv cnnvnm ubth bilanri cdm dmmptd eleq2d funfvima sylan syldan
        biimpar eleqtrrdi rspcv cnnvba nmblore simplr cexp adantl ipidsq resqcl
        c2 sqge0 absidd sqvald 3eqtrd nmblolbi eqbrtrrd lemul1ad lemul1 biimprd
        w3a 3expia expdimp syl21anc mpid 0red nmooge0 breq1 wo 0re leloe mpjaod
        blof com23 ralrimdva reximdva nmobndi mpbird ltpnf isblo mp2an sylanbrc
        ) AHLUGZHIIUHUIZUJZUKULUMZHFUGZUCAUXIUNUGZUXJAUXLBUOZMUJZUPUQUMZUXMHUJZ
        MUJZCUOZUQUMZURZBOUSZCUNUTZAEUOZINUHUIZUJZUXRUQUMZEKUSZCUNUTZUYBAUXMUYC
        UJZVDUJZDUOZUQUMEKUSDUNUTZBOUSZUYHAUYLBOAUXMOUGZVAZUXQUNUGZUYJUXQUQUMZE
        KUSUYLUYOIVBUGZUXPOUGZUYPIUAVCZAOOUXMHAUXGOOHVPZUCUYRUYRUXGVUAUYTUYTHIL
        IOOPPRVEVFVQZVGZUXPIMOPTVHVIZUYOUYQEKUYOUYCKUGZUXRJUJZUYCVJZCUYKMUJZUPU
        QUMZDOVKZUTZUYQUYOVUEVUKUYOJVLZUYCJVUJVMZUGVUKVUEAVULUYNAOINVNUIZJADOEO
        UYCUYKHUJZGUIZVOZVUNJAUYKOUGVAVUOOUGVUQVUNUGAOOUYKHVUBVGEVUOVUNNGIVUQOP
        QIVRUGZIVSUGUAIVTWAZUBVUNWBZVUQWBWCVQZUEWDZWEZWHVUEUYCKVUMVUEWIUFWFCUYC
        VUJJWGWJWKUYOVUGUYQCVUJUYOUXRVUJUGZVAUXMVUFUJZVDUJZUXQUQUMZVUGUYQVVDUYO
        UXROUGZUXRMUJZUPUQUMZVAZVVGVUIVVJDUXRODCWLZVUHVVIUPUQUYKUXRMWMWNWOUYOVV
        KVAZVVFUXPUXRGUIZVDUJZUXQUQVVMVVEVVNVDVVMVVEUXMUXRHUJZGUIZVVNUYNVVHVVEV
        VQVJAVVJVVHUYNVVEUXMEOUYCVVPGUIZVOZUJVVQVVHUXMVUFVVSEDVVRWPJVUQOOIUXRVV
        LEOVUPVVRVVLVUOVVPUYCGUYKUXRHWMWQWRUEPWSWTEUXMVVRVVQOVVSUYCUXMVVPGXAVVS
        WBUXMVVPGXBXCXDXEUYOVVHVVQVVNVJZVVJAUYNVVHVVTAVVTCOUSBOUSUYNVVHVAVVTURU
        DVVTBCOOXFVQXGXKXHXIVVMVVOUXQVVIXJUIZUXQVVMVVNUYOUYSVVHVVNYLUGZVVKVUCVV
        HVVJXLZUYRUYSVVHVWBUYTUXPUXRGIOPQXMXNWJXOVVMUXQVVIUYOUYPVVKVUDWHZVVHVVI
        UNUGZUYOVVJUYRVVHVWEUYTUXRIMOPTVHXPXQZXRVWDUYOUYSVVHVVOVWAUQUMVVKVUCVWC
        UXPUXRGIMOPTQVUSXSWJVVMVWAUXQUPXJUIZUXQUQVVMVWEUPUNUGUYPYBUXQUQUMZVAZVV
        JVWAVWGUQUMVWFVVMXTUYOVWIVVKUYOUYPVWHVUDUYOUYRUYSVWHUYTVUCUXPIMOPTYAZVI
        YCWHUYOVVHVVJYDVVIUPUXQYEYFVVMUXQVVMUXQVWDYGYHYIYMYJUUAVUGVVFUYJUXQUQVU
        GVVEUYIVDUXMVUFUYCUUBXIWNYKUUDYNUUCDEUYJUXQUQUNKUUEYOUUFAKVUNUUGZUYMUYH
        YPZAKJUUHZVUNKVUMVWMUFJVUJUUIUUJAOVUNJVVBUUKUUNIUULUGZNVBUGZVWKVWLVURVW
        NUAIUUMWANUBUUOZBEKIUYDVDNODCPNUBUUPZUYDWBZUUQVFVQYQAUYGUYACUNAUXRUNUGZ
        VAZUYGUXTBOVWTUYNVAUXOUYGUXSVWTUYNUXOUYGUXSURVWTUYNUXOVAZVAZUYGUXMJUJZU
        YDUJZUXRUQUMZUXSVXBVXCKUGUYGVXEURVXBVXCVUMKVXBUXMVUJUGZVXCVUMUGZVXFVXAV
        WTVUIUXODUXMODBWLZVUHUXNUPUQUYKUXMMWMWNWOUURAUYNVXFVXGURZVWSUXOAUYNUXMJ
        UUSZUGZVXIAVXKUYNAVXJOUXMADJOVUQVUNUEVVAUUTUVAUVEAVULVXKVXIVVCVUJUXMJUV
        BUVCUVDYRYSUFUVFUYFVXEEVXCKUYCVXCVJUYEVXDUXRUQUYCVXCUYDWMWNUVGVQVWTUYNV
        XEUXSURUXOVWTUYNVXEUXSVWTUYNVXEVAZVAZYBUXQULUMZUXSYBUXQVJZVXMVXNUXQUXQX
        JUIZUXRUXQXJUIZUQUMZUXSVXMVXPVXDUXQXJUIZVXQVXMUXQUXQAUYNUYPVWSVXEVUDYRZ
        VXTXRVXMVXDUXQAUYNVXDUNUGZVWSVXEUYOVXCVUNUGZVYAAOVUNUXMJVVBVGZUYRVWOVYB
        VYAUYTVWPVUNVXCIUYDNOYLPNUBUVHZVWRVUTUVIVFVQYRZVXTXRVXMUXRUXQAVWSVXLUVJ
        ZVXTXRVXMUXPVXCUJZVDUJZVXPVXSUQVXMVYHUXQUVOUVKUIZVDUJZVYIVXPVXMVYGVYIVD
        VXMVYGUXPUXPGUIZVYIAUYNVYGVYKVJVWSVXEUYOVYGUXPEOUYCUXPGUIZVOZUJZVYKUYOU
        XPVXCVYMUYNVXCVYMVJAEDVYLWPJVUQOOIUXMVXHEOVUPVYLVXHVUOUXPUYCGUYKUXMHWMW
        QWRUEPWSUVLWTUYOUYSVYNVYKVJVUCEUXPVYLVYKOVYMUYCUXPUXPGXAVYMWBUXPUXPGXBX
        CVQXHYRVXMUYRUYSVYKVYIVJUYTAUYNUYSVWSVXEVUCYRZUXPGIMOPTQUVMVIXHXIVXMUYP
        VYJVYIVJVXTUYPVYIUXQUVNUXQUVPUVQVQVXMUXQVXMUXQVXTYGUVRUVSVXMVYBUYSVYHVX
        SUQUMAUYNVYBVWSVXEVYCYRVYOUXPVUNVXCIMVDUYDNOPTVWQVWRVUTUYTVWPUVTYOUWAVX
        MVXDUXRUXQVYEVYFVXTVXMUYRUYSVWHUYTVYOVWJVIZVWTUYNVXEYDZUWBYMVXMUYPVWSUY
        PVXNVXRUXSURZURVXTVYFVXTUYPVWSVAUYPVXNVYRUYPVWSUYPVXNVAZVYRUYPVWSVYSUWE
        UXSVXRUXQUXRUXQUWCUWDUWFUWGUWHUWIVXMYBUXRUQUMVXOUXSVXMYBVXDUXRVXMUWJVYE
        VYFVXMOYLVXCVPZYBVXDUQUMZAUYNVYTVWSVXEUYOVYBVYTVYCUYRVWOVYBVYTUYTVWPVUN
        VXCINOYLPVYDVUTUWQVFVQYRUYRVWOVYTWUAUYTVWPVXCIUYDNOYLPVYDVWRUWKVFVQVYQY
        MYBUXQUXRUQUWLYKVXMVWHVXNVXOUWMZVYPVXMYBUNUGUYPVWHWUBYPUWNVXTYBUXQUWOVI
        YQUWPYTXKYNYTUWRUWSUWTYSAVUAUXLUYBYPVUBBHIMMUXHIOOCPPTTUXHWBZUYTUYTUXAV
        QUXBUXIUXCVQUYRUYRUXKUXGUXJVAYPUYTUYTFHILUXHIWUCRSUXDUXEUXF $.
    $}

    $( Hellinger-Toeplitz Theorem: any self-adjoint linear operator defined on
       all of Hilbert space is bounded.  Theorem 10.1-1 of [Kreyszig] p. 525.
       Discovered by E. Hellinger and O. Toeplitz in 1910, "it aroused both
       admiration and puzzlement since the theorem establishes a relation
       between properties of two different kinds, namely, the properties of
       being defined everywhere and being bounded."  (Contributed by NM,
       11-Jan-2008.)  (Revised by Mario Carneiro, 23-Aug-2014.)
       (New usage is discouraged.) $)
    htth $p |- ( ( U e. CHilOLD /\ T e. L /\
        A. x e. X A. y e. X ( x P ( T ` y ) ) = ( ( T ` x ) P y ) ) ->
      T e. B ) $=
      ( vw cv cfv co wceq wral fveq2 eqid vu vv vz chlo wcel wa caddc cmul cabs
      wi cop cif clno cdip cba cblo oveq12 anidms eqtrid eleq2d oveqd raleqbidv
      eqeq12d anbi12d imbi12d cmpt cnmcv c1 cle wbr crab cima cnchl simpl oveq1
      elimel oveq1d oveq2d oveq2 bilani cbvmptv mpteq2dv breq1d cbvrabv imaeq2i
      cbvral2vw htthlem dedth 3impib ) FUDUEZEGUEZANZBNZEOZDPZWLEOZWMDPZQZBHRZA
      HRZECUEZWJWKWTUFZXAUJEWJFUGUHUKUIUKZULZXDUMPZUEZWLWNXDUNOZPZWPWMXGPZQZBXD
      UOOZRZAXKRZUFZEXDXDUPPZUEZUJFXCFXDQZXBXNXAXPXQWKXFWTXMXQGXEEXQGFFUMPZXEKX
      QXRXEQFXDFXDUMUQURUSUTXQWSXLAHXKXQHFUOOXKIFXDUOSUSZXQWRXJBHXKXSXQWOXHWQXI
      XQDXGWLWNXQDFUNOXGJFXDUNSUSZVAXQDXGWPWMXTVAVCVBVBVDXQCXOEXQCFFUPPZXOLXQYA
      XOQFXDFXDUPUQURUSUTVEXNUAUBUCMXOXGEXDAXKBXKWMWPXGPZVFZVFZYDWLXDVGOZOZVHVI
      VJZAXKVKZVLXEYEXCXKXKTXGTXETXOTYETFXCUDXCXCTZVMVPYIXFXMVNXMUANZUBNZEOZXGP
      ZYJEOZYKXGPZQZUBXKRUAXKRXFXJYPYJWNXGPZYNWMXGPZQABUAUBXKXKWLYJQZXHYQXIYRWL
      YJWNXGVOYSWPYNWMXGWLYJESVQVCWMYKQZYQYMYRYOYTWNYLYJXGWMYKESVRWMYKYNXGVSVCW
      FVTAUCXKYCMXKMNZUCNZEOZXGPZVFZWLUUBQZYCMXKUUAWPXGPZVFUUEBMXKYBUUGWMUUAWPX
      GVOWAUUFMXKUUGUUDUUFWPUUCUUAXGWLUUBESVRWBUSWAYHUUBYEOZVHVIVJZUCXKVKYDYGUU
      IAUCXKUUFYFUUHVHVIWLUUBYESWCWDWEWGWHWI $.
  $}
$( End $[ set-deprec.mm $] $)


$( Begin $[ set-typeset.mm $] $)
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Appendix:  Typesetting definitions for the tokens in this file
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( $t

/* The '$ t' (no space between '$' and 't') token indicates the beginning
    of the typesetting definition section, embedded in a Metamath
    comment.  There may only be one per source file, and the typesetting
    section ends with the end of the Metamath comment.  The typesetting
    section uses C-style comment delimiters.  TODO:  Allow multiple
    typesetting comments */

/* These are the LaTeX and HTML definitions in the order the tokens are
    introduced in $c or $v statements.  See HELP TEX or HELP HTML in the
    Metamath program. */

/* Note that the ALT= fields in htmldefs should be preceded by a space.  This
   ensures that a screen copy from the web page will have a space between
   symbols. */
/* Math font table with XITS and LaTeX defs:
   http://meeting.contextgarden.net/2011/talks/day3_05_ulrik_opentype/Samples/
           unimath-symbols.pdf */


/******* Web page format settings *******/

/* Custom CSS for Unicode fonts */
/* The woff font file was obtained from
   http://fred-wang.github.io/MathFonts/XITS/xits-math.woff 28-Aug-2015 */
htmlcss '<STYLE TYPE="text/css">\n' +
    '<!--\n' +
    '  .setvar { color: red; }\n' +
    '  .wff { color: blue; }\n' +
    '  .class { color: #C3C; }\n' +
    '  .symvar { border-bottom:1px dotted;color:#C3C}\n' +
    '  .typecode { color: gray }\n' +
    '  .hidden { color: gray }\n' +
    '  @font-face {\n' +
    '    font-family: XITSMath-Regular;\n' +
    '    src: url(xits-math.woff);\n' +
    '  }\n' +
    '  .math { font-family: XITSMath-Regular }\n' +
    '-->\n' +
    '</STYLE>\n' +
    '<LINK href="mmset.css" title="mmset"\n' +
    '    rel="stylesheet" type="text/css">\n' +
    '<LINK href="mmsetalt.css" title="mmsetalt"\n' +
    '    rel="alternate stylesheet" type="text/css">';

/* Tag(s) for the main SPAN surrounding all Unicode math */
htmlfont 'CLASS=math';

/* Page title, home page link */
htmltitle "Metamath Proof Explorer";
htmlhome '<A HREF="mmset.html"><FONT SIZE=-2 FACE=sans-serif>' +
    '<IMG SRC="mm.gif" BORDER=0 ALT='  +
    '"Home" HEIGHT=32 WIDTH=32 ALIGN=MIDDLE STYLE="margin-bottom:0px">' +
    'Home</FONT></A>';
/* Optional file where bibliographic references are kept */
/* If specified, e.g., "mmset.html", Metamath will hyperlink all strings of the
   form "[rrr]" (where "rrr" has no whitespace) to "mmset.html#rrr" */
/* A warning will be given if the file "mmset.html" with the bibliographical
   references is not present.  It is read in order to check existence of
   the references. */
htmlbibliography "mmset.html";

/* Page title, home page link */
/* These are the variables used for the Hilbert Space extension to
   set.mm. */
exthtmltitle "Hilbert Space Explorer";
exthtmlhome '<A HREF="mmhil.html"><FONT SIZE=-2 FACE=sans-serif>' +
    '<IMG SRC="atomic.gif" BORDER=0 ALT='  +
    '"Home" HEIGHT=32 WIDTH=32 ALIGN=MIDDLE STYLE="margin-bottom:0px">' +
    'Home</FONT></A>';
/* The variable "exthtmllabel" means that all states including
   and after this label should use the "ext..." variables. */
exthtmllabel "chba";
/* A warning will be given if the file with the bibliographical references
   is not present. */
exthtmlbibliography "mmhil.html";

/* Variable color key at the bottom of each proof table */
htmlvarcolor '<SPAN CLASS=wff STYLE="color:blue;font-style:normal">wff</SPAN> '
    + '<SPAN CLASS=setvar STYLE="color:red;font-style:normal">setvar</SPAN> '
    + '<SPAN CLASS=class STYLE="color:#C3C;font-style:normal">class</SPAN>';

/* GIF and Unicode HTML directories - these are used for the GIF version to
   crosslink to the Unicode version and vice-versa */
htmldir "../mpegif/";
althtmldir "../mpeuni/";

/* Optional link(s) to other versions of the theorem page.  A "*" is replaced
   with the label of the current theorem.  If you need a literal "*" as part
   of the URL, use the alternate URL encoding "%2A". */
htmlexturl '<A HREF="http://metamath.tirix.org/mpests/*.html">'
    + 'Structured version</A>&nbsp;&nbsp; '
    + '<A HREF="https://expln.github.io/metamath/asrt/*.html">'
    + 'Visualization version</A>&nbsp;&nbsp; ';


/******* Symbol definitions *******/

htmldef "(" as "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT=' (' TITLE='('>";
  althtmldef "(" as "(";
  latexdef "(" as "(";
htmldef ")" as "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 ALT=' )' TITLE=')'>";
  althtmldef ")" as ")";
  latexdef ")" as ")";
htmldef "->" as
    " <IMG SRC='to.gif' WIDTH=15 HEIGHT=19 ALT=' -&gt;' TITLE='-&gt;'> ";
  althtmldef "->" as " &rarr; ";
  latexdef "->" as " \rightarrow ";
htmldef "-." as
    "<IMG SRC='lnot.gif' WIDTH=10 HEIGHT=19 ALT=' -.' TITLE='-.'> ";
  althtmldef "-." as '&not; ';
  latexdef "-." as "\lnot";
htmldef "wff" as
    "<IMG SRC='_wff.gif' WIDTH=24 HEIGHT=19 ALT=' wff' TITLE='wff'> ";
  althtmldef "wff" as
    '<SPAN CLASS=typecode STYLE="color:gray">wff </SPAN>'; /* was #00CC00 */
  latexdef "wff" as "\mathrm{wff}";
htmldef "|-" as
    "<IMG SRC='_vdash.gif' WIDTH=10 HEIGHT=19 ALT=' |-' TITLE='|-'> ";
  althtmldef "|-" as
    '<SPAN CLASS=hidden STYLE="color:gray">&#8866; </SPAN>'; /* &vdash; */
    /* Without sans-serif, way too big in FF3 */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|-" as "\vdash";
htmldef "&" as
    " <IMG SRC='amp.gif' WIDTH=12 HEIGHT=19 ALT='&amp;'> ";
  althtmldef "&" as " &amp; ";
  latexdef "&" as "\mathrel{\&}";
htmldef "=>" as
  " <IMG SRC='bigto.gif' WIDTH=15 HEIGHT=19 ALT='=&gt;'> ";
  althtmldef "=>" as " &rArr; ";
  latexdef "=>" as " \Rightarrow ";
htmldef "ph" as
    "<IMG SRC='_varphi.gif' WIDTH=11 HEIGHT=19 ALT=' ph' TITLE='ph'>";
  /* althtmldef "ph" as '<FONT COLOR="#0000FF">&#x1D711;</SPAN>'; */
  althtmldef "ph" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D711;</SPAN>';
  latexdef "ph" as "\varphi";
htmldef "ps" as "<IMG SRC='_psi.gif' WIDTH=12 HEIGHT=19 ALT=' ps' TITLE='ps'>";
  althtmldef "ps" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D713;</SPAN>';
  latexdef "ps" as "\psi";
htmldef "ch" as "<IMG SRC='_chi.gif' WIDTH=12 HEIGHT=19 ALT=' ch' TITLE='ch'>";
  althtmldef "ch" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D712;</SPAN>';
  latexdef "ch" as "\chi";
htmldef "th" as
    "<IMG SRC='_theta.gif' WIDTH=8 HEIGHT=19 ALT=' th' TITLE='th'>";
  althtmldef "th" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D703;</SPAN>';
  latexdef "th" as "\theta";
htmldef "ta" as "<IMG SRC='_tau.gif' WIDTH=10 HEIGHT=19 ALT=' ta' TITLE='ta'>";
  althtmldef "ta" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D70F;</SPAN>';
  latexdef "ta" as "\tau";
htmldef "et" as "<IMG SRC='_eta.gif' WIDTH=9 HEIGHT=19 ALT=' et' TITLE='et'>";
  althtmldef "et" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D702;</SPAN>';
  latexdef "et" as "\eta";
htmldef "ze" as "<IMG SRC='_zeta.gif' WIDTH=9 HEIGHT=19 ALT=' ze' TITLE='ze'>";
  althtmldef "ze" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D701;</SPAN>';
  latexdef "ze" as "\zeta";
htmldef "si" as
    "<IMG SRC='_sigma.gif' WIDTH=10 HEIGHT=19 ALT=' si' TITLE='si'>";
  althtmldef "si" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70E;</SPAN>';
  latexdef "si" as "\sigma";
htmldef "rh" as "<IMG SRC='_rho.gif' WIDTH=9 HEIGHT=19 ALT=' rh' TITLE='rh'>";
  althtmldef "rh" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D70C;</SPAN>';
  latexdef "rh" as "\rho";
htmldef "mu" as "<IMG SRC='_mu.gif' WIDTH=10 HEIGHT=19 ALT=' mu' TITLE='mu'>";
  althtmldef "mu" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D707;</SPAN>';
  latexdef "mu" as "\mu";
htmldef "la" as
    "<IMG SRC='_lambda.gif' WIDTH=9 HEIGHT=19 ALT=' la' TITLE='la'>";
  althtmldef "la" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D706;</SPAN>';
  latexdef "la" as "\lambda";
htmldef "ka" as
    "<IMG SRC='_kappa.gif' WIDTH=9 HEIGHT=19 ALT=' ka' TITLE='ka'>";
  althtmldef "ka" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D705;</SPAN>';
  latexdef "ka" as "\kappa";
htmldef "nu" as
    "<IMG SRC='_nu.gif' WIDTH=9 HEIGHT=19 ALT=' nu' TITLE='nu'>";
  althtmldef "nu" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D708;</SPAN>';
  latexdef "nu" as "\nu";
htmldef "<->" as " <IMG SRC='leftrightarrow.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' &lt;-&gt;' TITLE='&lt;-&gt;'> ";
  althtmldef "<->" as ' &harr; ';
  latexdef "<->" as "\leftrightarrow";
htmldef "\/" as
     " <IMG SRC='vee.gif' WIDTH=11 HEIGHT=19 ALT=' \/' TITLE='\/'> ";
  althtmldef "\/" as ' &or; ' ;
    /* althtmldef "\/" as ' <FONT FACE=sans-serif>&#8897;</FONT> ' ; */
    /* was &or; - changed to match font of &and; replacement */
    /* Changed back 6-Mar-2012 NM */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "\/" as "\vee";
htmldef "/\" as
    " <IMG SRC='wedge.gif' WIDTH=11 HEIGHT=19 ALT=' /\' TITLE='/\'> ";
  althtmldef "/\" as ' &and; ';
    /* althtmldef "/\" as ' <FONT FACE=sans-serif>&#8896;</FONT> '; */
    /* was &and; which is circle in Mozilla on WinXP Pro (but not Home) */
    /* Changed back 6-Mar-2012 NM */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "/\" as "\wedge";
htmldef "-/\" as
    " <IMG SRC='barwedge.gif' WIDTH=9 HEIGHT=19 ALT=' -/\' TITLE='-/\'> ";
  althtmldef "-/\" as ' &#8892; ';
    /*althtmldef "-/\" as " &#8892; "; */ /* too-high font bug in FF */
    /* barwedge, U022BC, alias ISOAMSB barwed, ['nand'] */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "-/\" as "\barwedge";
htmldef "\/_" as
    " <IMG SRC='veebar.gif' WIDTH=9 HEIGHT=19 ALT=' \/_' TITLE='\/_'> ";
  althtmldef "\/_" as " &#8891; ";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "\/_" as "\mathrel{\underline{\vee}}";
htmldef "-\/" as
    " <IMG SRC='vee.gif' WIDTH=9 HEIGHT=19 ALT=' -\/' TITLE='-\/' " +
    " STYLE='text-decoration:overline;'> ";
  althtmldef "-\/" as
    ' <span>&#8893;</span> ';
  latexdef "-\/" as "\mathrel{\overline{\vee}}";
htmldef "T." as
    " <IMG SRC='top.gif' WIDTH=11 HEIGHT=19 ALT='T.' TITLE='T.'> ";
  althtmldef "T." as '&#x22A4;';
  latexdef "T." as "\top";
htmldef "F." as
    " <IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 ALT='F.' TITLE='F.'> ";
  althtmldef "F." as '&perp;';
  latexdef "F." as "\bot";
htmldef "hadd" as "hadd";
  althtmldef "hadd" as "hadd";
  latexdef "hadd" as "\text{ hadd }";
htmldef "cadd" as "cadd";
  althtmldef "cadd" as "cadd";
  latexdef "cadd" as "\text{ cadd }";
htmldef "A." as
    "<IMG SRC='forall.gif' WIDTH=10 HEIGHT=19 ALT=' A.' TITLE='A.'>";
  althtmldef "A." as '&forall;'; /* &#8704; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "A." as "\forall";
htmldef "setvar" as
    "<IMG SRC='_setvar.gif' WIDTH=40 HEIGHT=19 ALT=' setvar' TITLE='setvar'> ";
  althtmldef
    "setvar" as '<SPAN CLASS=typecode STYLE="color:gray">setvar </SPAN>';
  latexdef "setvar" as "\mathrm{setvar}";
htmldef "x" as "<IMG SRC='_x.gif' WIDTH=10 HEIGHT=19 ALT=' x' TITLE='x'>";
  /* http://www.unicode.org/charts/PDF/U1D400.pdf has math italic Unicode */
  althtmldef "x" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D465;</SPAN>';
  latexdef "x" as "x";
htmldef "y" as "<IMG SRC='_y.gif' WIDTH=9 HEIGHT=19 ALT=' y' TITLE='y'>";
  althtmldef "y" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D466;</SPAN>';
  latexdef "y" as "y";
htmldef "z" as "<IMG SRC='_z.gif' WIDTH=9 HEIGHT=19 ALT=' z' TITLE='z'>";
  althtmldef "z" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D467;</SPAN>';
  latexdef "z" as "z";
htmldef "w" as "<IMG SRC='_w.gif' WIDTH=12 HEIGHT=19 ALT=' w' TITLE='w'>";
  althtmldef "w" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D464;</SPAN>';
  latexdef "w" as "w";
htmldef "v" as "<IMG SRC='_v.gif' WIDTH=9 HEIGHT=19 ALT=' v' TITLE='v'>";
  althtmldef "v" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D463;</SPAN>';
  latexdef "v" as "v";
htmldef "u" as "<IMG SRC='_u.gif' WIDTH=10 HEIGHT=19 ALT=' u' TITLE='u'>";
  althtmldef "u" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D462;</SPAN>';
  latexdef "u" as "u";
htmldef "t" as "<IMG SRC='_t.gif' WIDTH=7 HEIGHT=19 ALT=' t' TITLE='t'>";
  althtmldef "t" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D461;</SPAN>';
  latexdef "t" as "t";
htmldef "E." as
    "<IMG SRC='exists.gif' WIDTH=9 HEIGHT=19 ALT=' E.' TITLE='E.'>";
  althtmldef "E." as '&exist;'; /* &#8707; */
    /* Without sans-serif, bad in Opera and way too big in FF3 */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "E." as "\exists";
htmldef "F/" as
    "<IMG SRC='finv.gif' WIDTH=9 HEIGHT=19 ALT=' F/' TITLE='F/'>";
  althtmldef "F/" as "&#8498;";
  latexdef "F/" as "\Finv";
htmldef "class" as
    "<IMG SRC='_class.gif' WIDTH=32 HEIGHT=19 ALT=' class' TITLE='class'> ";
  althtmldef "class" as
    '<SPAN CLASS=typecode STYLE="color:gray">class </SPAN>';
  latexdef "class" as "\mathrm{class}";
htmldef "=" as " <IMG SRC='eq.gif' WIDTH=12 HEIGHT=19 ALT=' =' TITLE='='> ";
  althtmldef "=" as ' = '; /* &equals; */
  latexdef "=" as "=";
htmldef "e." as " <IMG SRC='in.gif' WIDTH=10 HEIGHT=19 ALT=' e.' TITLE='e.'> ";
  althtmldef "e." as ' &isin; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "e." as "\in";
htmldef "[" as "<IMG SRC='lbrack.gif' WIDTH=5 HEIGHT=19 ALT=' [' TITLE='['>";
  althtmldef "[" as '['; /* &lsqb; */
  latexdef "[" as "[";
htmldef "/" as
    " <IMG SRC='solidus.gif' WIDTH=6 HEIGHT=19 ALT=' /' TITLE='/'> ";
  althtmldef "/" as ' / '; /* &sol; */
  latexdef "/" as "/";
htmldef "]" as "<IMG SRC='rbrack.gif' WIDTH=5 HEIGHT=19 ALT=' ]' TITLE=']'>";
  althtmldef "]" as ']'; /* &rsqb; */
  latexdef "]" as "]";
htmldef "E!" as "<IMG SRC='_e1.gif' WIDTH=12 HEIGHT=19 ALT=' E!' TITLE='E!'>";
  althtmldef "E!" as '&exist;!';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "E!" as "\exists{!}";
htmldef "E*" as "<IMG SRC='_em1.gif' WIDTH=15 HEIGHT=19 ALT=' E*' TITLE='E*'>";
  althtmldef "E*" as '&exist;*';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "E*" as "\exists^\ast";
htmldef "{" as "<IMG SRC='lbrace.gif' WIDTH=6 HEIGHT=19 ALT=' {' TITLE='{'>";
  althtmldef "{" as '{'; /* &lcub; */
  latexdef "{" as "\{";
htmldef "|" as " <IMG SRC='vert.gif' WIDTH=3 HEIGHT=19 ALT=' |' TITLE='|'> ";
  althtmldef "|" as ' &#8739; '; /* &vertbar; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|" as "|";
htmldef "}" as "<IMG SRC='rbrace.gif' WIDTH=6 HEIGHT=19 ALT=' }' TITLE='}'>";
  althtmldef "}" as '}'; /* &rcub; */
  latexdef "}" as "\}";
htmldef "F/_" as
    "<IMG SRC='_finvbar.gif' WIDTH=9 HEIGHT=19 ALT=' F/_' TITLE='F/_'>";
  althtmldef "F/_" as "<U>&#8498;</U>";
  latexdef "F/_" as "\underline{\Finv}";
htmldef "CondEq" as "CondEq";
  althtmldef "CondEq" as "CondEq";
  latexdef "CondEq" as "\text{ CondEq }";
htmldef "./\" as
    " <IMG SRC='_.wedge.gif' WIDTH=11 HEIGHT=19 ALT=' ./\' TITLE='./\'> ";
  althtmldef "./\" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&and;</SPAN> ';
  latexdef "./\" as "\wedge";
htmldef ".\/" as
    " <IMG SRC='_.vee.gif' WIDTH=11 HEIGHT=19 ALT=' .\/' TITLE='.\/'> ";
  althtmldef ".\/" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&or;</SPAN> ';
  latexdef ".\/" as "\vee";
htmldef ".<_" as
    " <IMG SRC='_.le.gif' WIDTH=11 HEIGHT=19 ALT=' .&lt;_' TITLE='.&lt;_'> ";
  althtmldef ".<_" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&le;</SPAN> ';
  latexdef ".<_" as "\le";
htmldef ".<" as     /* Symbol as variable */
    " <IMG SRC='_.lt.gif' WIDTH=11 HEIGHT=19 ALT=' .&lt;' TITLE='.&lt;'> ";
  althtmldef ".<" as
    /* This is how to put a dotted box around the symbol: */
    /* border means box around symbol; border-bottom underlines symbol */
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&lt;</SPAN> ';
    /* TODO: can this STYLE sequence be done with a CLASS? */
    /* Move the underline down 3px so it isn't too close to symbol */
    /*
    ' <SPAN STYLE="vertical-align:-3px">' +
    '<SPAN CLASS=symvar STYLE="text-decoration:underline dotted;color:#C3C">' +
    '<SPAN STYLE="vertical-align:3px">&lt;</SPAN></SPAN></SPAN> ';
    */
  latexdef ".<" as "<";
htmldef ".+" as
    " <IMG SRC='_.plus.gif' WIDTH=13 HEIGHT=19 ALT=' .+' TITLE='.+'> ";
  althtmldef ".+" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '+</SPAN> ';
  latexdef ".+" as "+";
htmldef ".-" as
    " <IMG SRC='_.minus.gif' WIDTH=11 HEIGHT=19 ALT=' .-' TITLE='.-'> ";
  althtmldef ".-" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&minus;</SPAN> ';
  latexdef ".-" as "-";
htmldef ".X." as
    " <IMG SRC='_.times.gif' WIDTH=9 HEIGHT=19 ALT=' .X.' TITLE='.X.'> ";
  althtmldef ".X." as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&times;</SPAN> ';
  latexdef ".X." as "\times";
htmldef "./" as
    " <IMG SRC='_.solidus.gif' WIDTH=8 HEIGHT=19 ALT=' ./' TITLE='./'> ";
  althtmldef "./" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '/</SPAN> ';
  latexdef "./" as "/";
htmldef ".^" as
    " <IMG SRC='_.uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' .^' TITLE='.^'> ";
  althtmldef ".^" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&uarr;</SPAN> ';
  latexdef ".^" as "\uparrow";
htmldef ".0." as
    " <IMG SRC='_.0.gif' WIDTH=8 HEIGHT=19 ALT=' .0.' TITLE='.0.'> ";
  althtmldef ".0." as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '0</SPAN> ';
  latexdef ".0." as "0";
htmldef ".1." as
    " <IMG SRC='_.1.gif' WIDTH=7 HEIGHT=19 ALT=' .1.' TITLE='.1.'> ";
  althtmldef ".1." as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '1</SPAN> ';
  latexdef ".1." as "1";
htmldef ".||" as
    " <IMG SRC='_.parallel.gif' WIDTH=5 HEIGHT=19 ALT=' .||' TITLE='.||'> ";
  althtmldef ".||" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#8741;</SPAN> ';
  latexdef ".||" as "\parallel";
htmldef ".~" as
    " <IMG SRC='_.sim.gif' WIDTH=13 HEIGHT=19 ALT=' .~' TITLE='.~'> ";
  althtmldef ".~" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x223C;</SPAN> ';
  latexdef ".~" as "\sim";
htmldef "._|_" as
    " <IMG SRC='_.perp.gif' WIDTH=11 HEIGHT=19 ALT=' ._|_' TITLE='._|_'> ";
  althtmldef "._|_" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#8869;</SPAN> ';
  latexdef "._|_" as "\perp";
htmldef ".+^" as
    " <IMG SRC='_.plushat.gif' WIDTH=11 HEIGHT=19 ALT=' .+^' TITLE='.+^'> ";
  althtmldef ".+^" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x2A23;</SPAN> ';       /* &plusacir; */
  latexdef ".+^" as "\mathbin{\hat{+}}";
htmldef ".+b" as
    " <IMG SRC='_.plusb.gif' WIDTH=14 HEIGHT=19 ALT=' .+b' TITLE='.+b'> ";
  althtmldef ".+b" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x271A;</SPAN> ';
  latexdef ".+b" as "\pmb{+}";
htmldef ".(+)" as
    " <IMG SRC='_.oplus.gif' WIDTH=13 HEIGHT=19 ALT=' .(+)' TITLE='.(+)'> ";
  althtmldef ".(+)" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x2295;</SPAN> ';
  latexdef ".(+)" as "\oplus";
htmldef ".*" as
    " <IMG SRC='_.ast.gif' WIDTH=7 HEIGHT=19 ALT=' .*' TITLE='.*'> ";
  althtmldef ".*" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&lowast;</SPAN> ';
  latexdef ".*" as "\ast";
/* TODO-AV (provide another gif?) */
htmldef ".o." as
    " <IMG SRC='circ.gif' WIDTH=4 HEIGHT=19 ALT=' .o.' TITLE='.o.'> ";
  althtmldef ".o." as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x26AC;</SPAN> ';
  latexdef ".o." as "\circ";
htmldef ".x." as
    " <IMG SRC='_.cdot.gif' WIDTH=4 HEIGHT=19 ALT=' .x.' TITLE='.x.'> ";
  althtmldef ".x." as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&middot;</SPAN> ';
  latexdef ".x." as "\cdot";
htmldef ".xb" as
    " <IMG SRC='_.bullet.gif' WIDTH=8 HEIGHT=19 ALT=' .xb' TITLE='.xb'> ";
  althtmldef ".xb" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x2219;</SPAN> ';
  latexdef ".xb" as "\bullet";
htmldef ".," as
    " <IMG SRC='_.comma.gif' WIDTH=4 HEIGHT=19 ALT=' .,' TITLE='.,'> ";
  althtmldef ".," as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    ',</SPAN> ';
  latexdef ".," as ",";
htmldef ".(x)" as
    " <IMG SRC='_.otimes.gif' WIDTH=13 HEIGHT=19 ALT=' .(x)' TITLE='.(x)'> ";
  althtmldef ".(x)" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x2297;</SPAN> ';
  latexdef ".(x)" as "\otimes";
htmldef ".0b" as
    " <IMG SRC='_.bf0.gif' WIDTH=9 HEIGHT=19 ALT=' .0b' TITLE='.0b'> ";
  althtmldef ".0b" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x1D7CE</SPAN> ';
  latexdef ".0b" as "\pmb{0}";
htmldef "A" as "<IMG SRC='_ca.gif' WIDTH=11 HEIGHT=19 ALT=' A' TITLE='A'>";
  althtmldef "A" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D434;</SPAN>';
  latexdef "A" as "A";
htmldef "B" as "<IMG SRC='_cb.gif' WIDTH=12 HEIGHT=19 ALT=' B' TITLE='B'>";
  althtmldef "B" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D435;</SPAN>';
  latexdef "B" as "B";
htmldef "C" as "<IMG SRC='_cc.gif' WIDTH=12 HEIGHT=19 ALT=' C' TITLE='C'>";
  althtmldef "C" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D436;</SPAN>';
  latexdef "C" as "C";
htmldef "D" as "<IMG SRC='_cd.gif' WIDTH=12 HEIGHT=19 ALT=' D' TITLE='D'>";
  althtmldef "D" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D437;</SPAN>';
  latexdef "D" as "D";
htmldef "P" as "<IMG SRC='_cp.gif' WIDTH=12 HEIGHT=19 ALT=' P' TITLE='P'>";
  althtmldef "P" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D443;</SPAN>';
  latexdef "P" as "P";
htmldef "Q" as "<IMG SRC='_cq.gif' WIDTH=12 HEIGHT=19 ALT=' Q' TITLE='Q'>";
  althtmldef "Q" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D444;</SPAN>';
  latexdef "Q" as "Q";
htmldef "R" as "<IMG SRC='_cr.gif' WIDTH=12 HEIGHT=19 ALT=' R' TITLE='R'>";
  althtmldef "R" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D445;</SPAN>';
  latexdef "R" as "R";
htmldef "S" as "<IMG SRC='_cs.gif' WIDTH=11 HEIGHT=19 ALT=' S' TITLE='S'>";
  althtmldef "S" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D446;</SPAN>';
  latexdef "S" as "S";
htmldef "T" as "<IMG SRC='_ct.gif' WIDTH=12 HEIGHT=19 ALT=' T' TITLE='T'>";
  althtmldef "T" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D447;</SPAN>';
  latexdef "T" as "T";
htmldef "U" as "<IMG SRC='_cu.gif' WIDTH=12 HEIGHT=19 ALT=' U' TITLE='U'>";
  althtmldef "U" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D448;</SPAN>';
  latexdef "U" as "U";
htmldef "e" as "<IMG SRC='_e.gif' WIDTH=8 HEIGHT=19 ALT=' e' TITLE='e'>";
  althtmldef "e" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D452;</SPAN>';
  latexdef "e" as "e";
htmldef "f" as "<IMG SRC='_f.gif' WIDTH=9 HEIGHT=19 ALT=' f' TITLE='f'>";
  althtmldef "f" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D453;</SPAN>';
  latexdef "f" as "f";
htmldef "g" as "<IMG SRC='_g.gif' WIDTH=9 HEIGHT=19 ALT=' g' TITLE='g'>";
  althtmldef "g" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D454;</SPAN>';
  latexdef "g" as "g";
htmldef "h" as "<IMG SRC='_h.gif' WIDTH=10 HEIGHT=19 ALT=' h' TITLE='h'>";
  althtmldef "h" as '<SPAN CLASS=setvar STYLE="color:red">&#x210E;</SPAN>';
  latexdef "h" as "h";
htmldef "i" as "<IMG SRC='_i.gif' WIDTH=6 HEIGHT=19 ALT=' i' TITLE='i'>";
  althtmldef "i" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D456;</SPAN>';
  latexdef "i" as "i";
htmldef "j" as "<IMG SRC='_j.gif' WIDTH=7 HEIGHT=19 ALT=' j' TITLE='j'>";
  althtmldef "j" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D457;</SPAN>';
  latexdef "j" as "j";
htmldef "k" as "<IMG SRC='_k.gif' WIDTH=9 HEIGHT=19 ALT=' k' TITLE='k'>";
  althtmldef "k" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D458;</SPAN>';
  latexdef "k" as "k";
htmldef "m" as "<IMG SRC='_m.gif' WIDTH=14 HEIGHT=19 ALT=' m' TITLE='m'>";
  althtmldef "m" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D45A;</SPAN>';
  latexdef "m" as "m";
htmldef "n" as "<IMG SRC='_n.gif' WIDTH=10 HEIGHT=19 ALT=' n' TITLE='n'>";
  althtmldef "n" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D45B;</SPAN>';
  latexdef "n" as "n";
htmldef "o" as "<IMG SRC='_o.gif' WIDTH=8 HEIGHT=19 ALT=' o' TITLE='o'>";
  althtmldef "o" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D45C;</SPAN>';
  latexdef "o" as "o";
htmldef "E" as "<IMG SRC='_ce.gif' WIDTH=13 HEIGHT=19 ALT=' E' TITLE='E'>";
  althtmldef "E" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D438;</SPAN>';
  latexdef "E" as "E";
htmldef "F" as "<IMG SRC='_cf.gif' WIDTH=13 HEIGHT=19 ALT=' F' TITLE='F'>";
  althtmldef "F" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;</SPAN>';
  latexdef "F" as "F";
htmldef "G" as "<IMG SRC='_cg.gif' WIDTH=12 HEIGHT=19 ALT=' G' TITLE='G'>";
  althtmldef "G" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43A;</SPAN>';
  latexdef "G" as "G";
htmldef "H" as "<IMG SRC='_ch.gif' WIDTH=14 HEIGHT=19 ALT=' H' TITLE='H'>";
  althtmldef "H" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43B;</SPAN>';
  latexdef "H" as "H";
htmldef "I" as "<IMG SRC='_ci.gif' WIDTH=8 HEIGHT=19 ALT=' I' TITLE='I'>";
  althtmldef "I" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43C;</SPAN>';
  latexdef "I" as "I";
htmldef "J" as "<IMG SRC='_cj.gif' WIDTH=10 HEIGHT=19 ALT=' J' TITLE='J'>";
  althtmldef "J" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43D;</SPAN>';
  latexdef "J" as "J";
htmldef "K" as "<IMG SRC='_ck.gif' WIDTH=14 HEIGHT=19 ALT=' K' TITLE='K'>";
  althtmldef "K" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43E;</SPAN>';
  latexdef "K" as "K";
htmldef "L" as "<IMG SRC='_cl.gif' WIDTH=10 HEIGHT=19 ALT=' L' TITLE='L'>";
  althtmldef "L" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;</SPAN>';
  latexdef "L" as "L";
htmldef "M" as "<IMG SRC='_cm.gif' WIDTH=15 HEIGHT=19 ALT=' M' TITLE='M'>";
  althtmldef "M" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D440;</SPAN>';
  latexdef "M" as "M";
htmldef "N" as "<IMG SRC='_cn.gif' WIDTH=14 HEIGHT=19 ALT=' N' TITLE='N'>";
  althtmldef "N" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D441;</SPAN>';
  latexdef "N" as "N";
htmldef "V" as "<IMG SRC='_cv.gif' WIDTH=12 HEIGHT=19 ALT=' V' TITLE='V'>";
  althtmldef "V" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;</SPAN>';
  latexdef "V" as "V";
htmldef "W" as "<IMG SRC='_cw.gif' WIDTH=16 HEIGHT=19 ALT=' W' TITLE='W'>";
  althtmldef "W" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44A;</SPAN>';
  latexdef "W" as "W";
htmldef "X" as "<IMG SRC='_cx.gif' WIDTH=13 HEIGHT=19 ALT=' X' TITLE='X'>";
  althtmldef "X" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44B;</SPAN>';
  latexdef "X" as "X";
htmldef "Y" as "<IMG SRC='_cy.gif' WIDTH=12 HEIGHT=19 ALT=' Y' TITLE='Y'>";
  althtmldef "Y" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44C;</SPAN>';
  latexdef "Y" as "Y";
htmldef "Z" as "<IMG SRC='_cz.gif' WIDTH=11 HEIGHT=19 ALT=' Z' TITLE='Z'>";
  althtmldef "Z" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44D;</SPAN>';
  latexdef "Z" as "Z";
htmldef "O" as "<IMG SRC='_co.gif' WIDTH=12 HEIGHT=19 ALT=' O' TITLE='O'>";
  althtmldef "O" as '<SPAN CLASS=class STYLE="color:#C3C">&#x1D442;</SPAN>';
  latexdef "O" as "O";
htmldef "s" as "<IMG SRC='_s.gif' WIDTH=7 HEIGHT=19 ALT=' s' TITLE='s'>";
  althtmldef "s" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D460;</SPAN>';
  latexdef "s" as "s";
htmldef "r" as "<IMG SRC='_r.gif' WIDTH=8 HEIGHT=19 ALT=' r' TITLE='r'>";
  althtmldef "r" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D45F;</SPAN>';
  latexdef "r" as "r";
htmldef "q" as "<IMG SRC='_q.gif' WIDTH=8 HEIGHT=19 ALT=' q' TITLE='q'>";
  althtmldef "q" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D45E;</SPAN>';
  latexdef "q" as "q";
htmldef "p" as "<IMG SRC='_p.gif' WIDTH=10 HEIGHT=19 ALT=' p' TITLE='p'>";
  althtmldef "p" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D45D;</SPAN>';
  latexdef "p" as "p";
htmldef "a" as "<IMG SRC='_a.gif' WIDTH=9 HEIGHT=19 ALT=' a' TITLE='a'>";
  althtmldef "a" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D44E;</SPAN>';
  latexdef "a" as "a";
htmldef "b" as "<IMG SRC='_b.gif' WIDTH=8 HEIGHT=19 ALT=' b' TITLE='b'>";
  althtmldef "b" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D44F;</SPAN>';
  latexdef "b" as "b";
htmldef "c" as "<IMG SRC='_c.gif' WIDTH=7 HEIGHT=19 ALT=' c' TITLE='c'>";
  althtmldef "c" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D450;</SPAN>';
  latexdef "c" as "c";
htmldef "d" as "<IMG SRC='_d.gif' WIDTH=9 HEIGHT=19 ALT=' d' TITLE='d'>";
  althtmldef "d" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D451;</SPAN>';
  latexdef "d" as "d";
htmldef "l" as "<IMG SRC='_l.gif' WIDTH=6 HEIGHT=19 ALT=' l' TITLE='l'>";
  althtmldef "l" as '<SPAN CLASS=setvar STYLE="color:red">&#x1D459;</SPAN>';
  latexdef "l" as "l";
htmldef "=/=" as
    " <IMG SRC='ne.gif' WIDTH=12 HEIGHT=19 ALT=' =/=' TITLE='=/='> ";
  althtmldef "=/=" as ' &ne; ';
  latexdef "=/=" as "\ne";
htmldef "e/" as
    " <IMG SRC='notin.gif' WIDTH=10 HEIGHT=19 ALT=' e/' TITLE='e/'> ";
  althtmldef "e/" as ' &notin; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "e/" as "\notin";
htmldef "_V" as "<IMG SRC='rmcv.gif' WIDTH=10 HEIGHT=19 ALT=' _V' TITLE='_V'>";
  althtmldef "_V" as 'V';
  latexdef "_V" as "\mathrm{V}";
htmldef "[." as
    "<IMG SRC='_dlbrack.gif' WIDTH=7 HEIGHT=19 ALT=' [.' TITLE='[.'>";
  /* althtmldef "[." as '&#x298F;'; */   /* corner tick */
  /* althtmldef "[." as '[&#803;'; */  /* combining dot below */
  althtmldef "[." as '<B>[</B>'; /* 6-Aug-2018 nm */
  latexdef "[." as "\text{\d{[}}";
htmldef "]." as
    "<IMG SRC='_drbrack.gif' WIDTH=6 HEIGHT=19 ALT=' ].' TITLE='].'>";
  /* althtmldef "]." as '&#x298E;'; */   /* corner tick */
  /* althtmldef "]." as ']&#803;'; */  /* combining dot below */
  althtmldef "]." as '<B>]</B>'; /* 6-Aug-2018 nm */
  latexdef "]." as "\text{\d{]}}";
htmldef "[_" as
    "<IMG SRC='_ulbrack.gif' WIDTH=7 HEIGHT=19 ALT=' [_' TITLE='[_'>";
  althtmldef "[_" as '<B>&#x298B;</B>'; /* left sq brack w underbar */
  latexdef "[_" as "\underline{[}";
htmldef "]_" as
    "<IMG SRC='_urbrack.gif' WIDTH=6 HEIGHT=19 ALT=' ]_' TITLE=']_'>";
  althtmldef "]_" as '<B>&#x298C;</B>'; /* right sq brack w underbar */
  latexdef "]_" as "\underline{]}";
htmldef "\" as
    " <IMG SRC='setminus.gif' WIDTH=8 HEIGHT=19 ALT=' \' TITLE='\'> ";
  althtmldef "\" as ' &#8726; '; /* &setmn; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "\" as "\setminus";
htmldef "u." as
    " <IMG SRC='cup.gif' WIDTH=10 HEIGHT=19 ALT=' u.' TITLE='u.'> ";
  althtmldef "u." as ' &cup; ';
  latexdef "u." as "\cup";
htmldef "i^i" as
    " <IMG SRC='cap.gif' WIDTH=10 HEIGHT=19 ALT=' i^i' TITLE='i^i'> ";
  althtmldef "i^i" as ' &cap; ';
  latexdef "i^i" as "\cap";
htmldef "C_" as
    " <IMG SRC='subseteq.gif' WIDTH=12 HEIGHT=19 ALT=' C_' TITLE='C_'> ";
  althtmldef "C_" as ' &#8838; '; /* &subE; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "C_" as "\subseteq";
    /* 7-Jun-2019 changed gif, unicode and latex def of "C." from subset to
    subsetneq (BJ) */
htmldef "C." as
    " <IMG SRC='subsetneq.gif' WIDTH=12 HEIGHT=19 ALT=' C.' TITLE='C.'> ";
    /* subset.gif */
  althtmldef "C." as ' &#x228a; '; /* &sub; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "C." as "\subsetneq"; /* \subset */
htmldef "(/)" as
    "<IMG SRC='varnothing.gif' WIDTH=11 HEIGHT=19 ALT=' (/)' TITLE='(/)'>";
  althtmldef "(/)" as '&empty;';
    /*althtmldef "(/)" as '&empty;';*/ /* =&#8709 */ /* bad in Opera */
    /*althtmldef "(/)" as '&#8960;';*/
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "(/)" as "\varnothing";
htmldef "if" as "<IMG SRC='_if.gif' WIDTH=11 HEIGHT=19 ALT=' if' TITLE='if'>";
  althtmldef "if" as 'if';
  latexdef "if" as "\mathrm{if}";
htmldef "," as "<IMG SRC='comma.gif' WIDTH=4 HEIGHT=19 ALT=' ,' TITLE=','> ";
  althtmldef "," as ', ';
  latexdef "," as ",";
htmldef "~P" as "<IMG SRC='scrp.gif' WIDTH=16 HEIGHT=19 ALT=' ~P' TITLE='~P'>";
  /* althtmldef "~P" as '<FONT FACE=sans-serif>&weierp;</FONT>'; */
  /* althtmldef "~P" as '&weierp;'; */ /* 2-Jan-2016 reverted sans-serif */
  /* 14-Jan-2016 script P is now available in upper Unicode */
  /* 4-Aug-2016 NM Put space after ~P, needed for, e.g., ncanth where it
     overlapped the _V */
  althtmldef "~P" as '&#119979; ';
  latexdef "~P" as "\mathcal{P}";
htmldef "<." as
    "<IMG SRC='langle.gif' WIDTH=4 HEIGHT=19 ALT=' &lt;.' TITLE='&lt;.'>";
    /* The Unicode below doesn't always work on Firefox and Chrome on Windows,
       so revert to the image above */
  althtmldef "<." as '&lang;'; /* &#9001; */
    /* 2-Jan-2016 restored Unicode; reverted sans-serif */
  latexdef "<." as "\langle";
htmldef ">." as
    "<IMG SRC='rangle.gif' WIDTH=4 HEIGHT=19 ALT=' &gt;.' TITLE='&gt;.'>";
    /* The Unicode below doesn't always work on Firefox and Chrome on Windows,
       so revert to the image above */
  althtmldef ">." as '&rang;'; /* &#9002; */
    /* 2-Jan-2016 restored Unicode; reverted sans-serif */
  latexdef ">." as "\rangle";
htmldef "U." as
    "<IMG SRC='bigcup.gif' WIDTH=13 HEIGHT=19 ALT=' U.' TITLE='U.'>";
  /* 20-Sep-2017 nm Add space after U. in althtmldef to improve "U. ran" */
  althtmldef "U." as '<FONT SIZE="+1">&cup;</FONT> '; /* &xcup; */
    /* xcup does not render, and #8899 renders as a small bold cup, on
       Mozilla 1.7.3 on Windows XP */
    /*althtmldef "U." as '&#8899;';*/ /* &xcup; */
  latexdef "U." as "\bigcup";
htmldef "|^|" as
    "<IMG SRC='bigcap.gif' WIDTH=13 HEIGHT=19 ALT=' |^|' TITLE='|^|'>";
  /* 20-Sep-2017 nm Add space after |^| in althtmldef to improve "|^| ran" */
  althtmldef "|^|" as '<FONT SIZE="+1">&cap;</FONT> '; /* &xcap; */
    /*althtmldef "|^|" as '&#8898;';*/ /* &xcap; */
  latexdef "|^|" as "\bigcap";
htmldef "U_" as
    "<IMG SRC='_cupbar.gif' WIDTH=13 HEIGHT=19 ALT=' U_' TITLE='U_'>";
  /* 20-Sep-2017 nm Add space after U_ in althtmldef to improve "U_ ran" */
  althtmldef "U_" as '<U><FONT SIZE="+1">&cup;</FONT></U> '; /* &xcup; */
  latexdef "U_" as "\underline{\bigcup}";
htmldef "|^|_" as
    "<IMG SRC='_capbar.gif' WIDTH=13 HEIGHT=19 ALT=' |^|_' TITLE='|^|_'>";
  /* 20-Sep-2017 nm Add space after |^|_ in althtmldef to improve "|^|_ ran" */
  althtmldef "|^|_" as '<U><FONT SIZE="+1">&cap;</FONT></U> '; /* &xcap; */
  latexdef "|^|_" as "\underline{\bigcap}";
htmldef "Disj_" as "<u>Disj</u> ";
  althtmldef "Disj_" as "<u>Disj</u> ";
  latexdef "Disj_" as "\operatorname{\underline{Disj}}";
htmldef "|->" as " <IMG SRC='mapsto.gif' WIDTH=15 HEIGHT=19 ALT=' |-&gt;'" +
    " TITLE='|-&gt;'> ";
  althtmldef "|->" as ' &#8614; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|->" as "\mapsto";
htmldef "Tr" as
    "<IMG SRC='_ctr.gif' WIDTH=16 HEIGHT=19 ALT=' Tr' TITLE='Tr'> ";
  althtmldef "Tr" as 'Tr ';
  latexdef "Tr" as "\mathrm{Tr}";
htmldef "_E" as
    " <IMG SRC='rmce.gif' WIDTH=9 HEIGHT=19 ALT=' _E' TITLE='_E'> ";
  althtmldef "_E" as ' E ';
  latexdef "_E" as "\mathrm{E}";
htmldef "_I" as
    " <IMG SRC='rmci.gif' WIDTH=4 HEIGHT=19 ALT=' _I' TITLE='_I'> ";
  althtmldef "_I" as ' I ';
  latexdef "_I" as "\mathrm{I}";
htmldef "Po" as
    " <IMG SRC='_po.gif' WIDTH=16 HEIGHT=19 ALT=' Po' TITLE='Po'> ";
  althtmldef "Po" as ' Po ';
  latexdef "Po" as "\mathrm{Po}";
htmldef "Or" as
    " <IMG SRC='_or.gif' WIDTH=18 HEIGHT=19 ALT=' Or' TITLE='Or'> ";
  althtmldef "Or" as ' Or ';
  latexdef "Or" as "\mathrm{Or}";
htmldef "Fr" as
    " <IMG SRC='_fr.gif' WIDTH=15 HEIGHT=19 ALT=' Fr' TITLE='Fr'> ";
  althtmldef "Fr" as ' Fr ';
  latexdef "Fr" as "\mathrel{\operatorname{Fr}}";
htmldef "Se" as ' Se ';
  althtmldef "Se" as ' Se ';
  latexdef "Se" as "\mathrel{\operatorname{Se}}";
htmldef "We" as
    " <IMG SRC='_we.gif' WIDTH=21 HEIGHT=19 ALT=' We' TITLE='We'> ";
  althtmldef "We" as ' We ';
  latexdef "We" as "\mathrm{We}";
htmldef "Ord" as
    "<IMG SRC='_ord.gif' WIDTH=26 HEIGHT=19 ALT=' Ord' TITLE='Ord'> ";
  althtmldef "Ord" as 'Ord ';
  latexdef "Ord" as "\mathrm{Ord}";
htmldef "On" as "<IMG SRC='_on.gif' WIDTH=20 HEIGHT=19 ALT=' On' TITLE='On'>";
  althtmldef "On" as 'On';
  latexdef "On" as "\mathrm{On}";
htmldef "Lim" as
    "<IMG SRC='_lim.gif' WIDTH=26 HEIGHT=19 ALT=' Lim' TITLE='Lim'> ";
  althtmldef "Lim" as 'Lim ';
  latexdef "Lim" as "\operatorname{Lim}";
htmldef "suc" as
    "<IMG SRC='_suc.gif' WIDTH=22 HEIGHT=19 ALT=' suc' TITLE='suc'> ";
  althtmldef "suc" as 'suc ';
  latexdef "suc" as "\operatorname{suc}";
htmldef "_om" as
    "<IMG SRC='omega.gif' WIDTH=11 HEIGHT=19 ALT=' om' TITLE='om'>";
  /*althtmldef "_om" as '&omega;';*/
  althtmldef "_om" as '&#x3C9;';  /* upright lowercase Greek omega */
  latexdef "_om" as "\mathrm{\omega}";
htmldef "X." as
    " <IMG SRC='times.gif' WIDTH=9 HEIGHT=19 ALT=' X.' TITLE='X.'> ";
  althtmldef "X." as ' &times; ';
  latexdef "X." as "\times";
htmldef "`'" as "<IMG SRC='_cnv.gif' WIDTH=10 HEIGHT=19 ALT=" + '"' + " `'" +
    '"' + "TITLE=" + '"' + "`'" + '"' + ">";
  althtmldef "`'" as '<FONT SIZE="-1"><SUP>&#9697;</SUP></FONT>'; /* or 8995 */
  latexdef "`'" as "{}^{\smallsmile}";
htmldef "dom" as
    "<IMG SRC='_dom.gif' WIDTH=26 HEIGHT=19 ALT=' dom' TITLE='dom'> ";
  althtmldef "dom" as 'dom ';
  latexdef "dom" as "\mathrm{dom}";
htmldef "ran" as
    "<IMG SRC='_ran.gif' WIDTH=22 HEIGHT=19 ALT=' ran' TITLE='ran'> ";
  althtmldef "ran" as 'ran ';
  latexdef "ran" as "\mathrm{ran}";
htmldef "|`" as " <IMG SRC='restriction.gif' WIDTH=5 HEIGHT=19 ALT=' |`'" +
    " TITLE='|`'> ";
  althtmldef "|`" as ' &#8638; '; /* &uharr; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|`" as "\restriction";
htmldef '"' as "<IMG SRC='backquote.gif' WIDTH=7 HEIGHT=19 ALT=' " + '"' +
    "' TITLE='" + '"' + "'>";
  althtmldef '"' as ' &ldquo; '; /* &#8220; */
  latexdef '"' as "``";
htmldef "o." as
    " <IMG SRC='circ.gif' WIDTH=8 HEIGHT=19 ALT=' o.' TITLE='o.'> ";
  althtmldef "o." as ' &#8728; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "o." as "\circ";
htmldef "Rel" as
    "<IMG SRC='_rel.gif' WIDTH=22 HEIGHT=19 ALT=' Rel' TITLE='Rel'> ";
  althtmldef "Rel" as 'Rel ';
  latexdef "Rel" as "\mathrm{Rel}";
htmldef "Fun" as
    "<IMG SRC='_fun.gif' WIDTH=25 HEIGHT=19 ALT=' Fun' TITLE='Fun'> ";
  althtmldef "Fun" as 'Fun ';
  latexdef "Fun" as "\mathrm{Fun}";
htmldef "Fn" as
    " <IMG SRC='_fn.gif' WIDTH=17 HEIGHT=19 ALT=' Fn' TITLE='Fn'> ";
  althtmldef "Fn" as ' Fn ';
  latexdef "Fn" as "\mathrm{Fn}";
htmldef ":" as "<IMG SRC='colon.gif' WIDTH=4 HEIGHT=19 ALT=' :' TITLE=':'>";
  althtmldef ":" as ':';
  latexdef ":" as ":";
htmldef "-->" as
  "<IMG SRC='longrightarrow.gif' WIDTH=23 HEIGHT=19 " +
    "ALT=' --&gt;' TITLE='--&gt;'>";
  /* althtmldef "-->" as '&ndash;&rarr;'; */
  althtmldef "-->" as '&#x27F6;';
    /* &#xAD;&#x2010;&ndash;&mdash;&minus; (possible symbols test) */
  latexdef "-->" as "\longrightarrow";
htmldef "-1-1->" as "<IMG SRC='onetoone.gif' WIDTH=23 HEIGHT=19 " +
    "ALT=' -1-1-&gt;' TITLE='-1-1-&gt;'>";
  althtmldef "-1-1->" as
    '&ndash;<FONT SIZE=-2 FACE=sans-serif>1-1</FONT>&rarr;';
  latexdef "-1-1->" as "\overset{\mathrm{1-1}}{\longrightarrow}";
htmldef "-onto->" as
    "<IMG SRC='onto.gif' WIDTH=23 HEIGHT=19 " +
    "ALT=' -onto-&gt;' TITLE='-onto-&gt;'>";
  althtmldef "-onto->" as
    '&ndash;<FONT SIZE=-2 FACE=sans-serif>onto</FONT>&rarr;';
  latexdef "-onto->" as "\underset{\mathrm{onto}}{\longrightarrow}";
htmldef "-1-1-onto->" as "<IMG SRC='onetooneonto.gif' WIDTH=23 HEIGHT=19 " +
    "ALT=' -1-1-onto-&gt;' TITLE='-1-1-onto-&gt;'>";
  althtmldef "-1-1-onto->" as '&ndash;<FONT SIZE=-2 '
    + 'FACE=sans-serif>1-1</FONT>-<FONT SIZE=-2 '
    + 'FACE=sans-serif>onto</FONT>&rarr;';
  latexdef "-1-1-onto->" as "\overset{\mathrm{1-1}}{\underset{\mathrm{onto}}" +
    "{\longrightarrow}}";
htmldef "`" as
    "<IMG SRC='backtick.gif' WIDTH=4 HEIGHT=19 ALT=' ` ' TITLE='` '>";
    /* Above, IE7 _printing_ is corrupted by '`'; use '` ' which works */
  /*althtmldef "`" as ' &lsquo;';*/
  /* I took out the leading space to make, e.g., ( log ` A ) look better.
     I added the leading space a long time ago because the quote overlapped
     the character to its left, making it sometimes hidden, but that seems
     to be no longer a problem with the XITS font. - 29-Aug-2017 nm */
  althtmldef "`" as '&lsquo;';
  latexdef "`" as "`";
htmldef "Isom" as " Isom ";
  althtmldef "Isom" as " Isom ";
  latexdef "Isom" as "\mathrm{Isom}";
htmldef "oF" as
    " <IMG SRC='circ.gif' WIDTH=8 HEIGHT=19 ALT=' o' TITLE='o'>" +
    "<IMG SRC='subf.gif' WIDTH=6 HEIGHT=19 ALT='F' TITLE='F'>";
  althtmldef "oF" as " &#8728;<SUB>f</SUB> ";
  latexdef "oF" as "\circ_\mathrm{f}";
htmldef "oR" as
    " <IMG SRC='circ.gif' WIDTH=8 HEIGHT=19 ALT=' o' TITLE='o'>" +
    "<IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 ALT='R' TITLE='R'>";
  althtmldef "oR" as " &#8728;<SUB>r</SUB> ";
  latexdef "oR" as "\circ_\mathrm{r}";
htmldef "1st" as
    "<IMG SRC='_1st.gif' WIDTH=15 HEIGHT=19 ALT=' 1st' TITLE='1st'>";
  althtmldef "1st" as '1<SUP>st</SUP> ';
  latexdef "1st" as "1^\mathrm{st}";
htmldef "2nd" as
    "<IMG SRC='_2nd.gif' WIDTH=21 HEIGHT=19 ALT=' 2nd' TITLE='2nd'>";
  althtmldef "2nd" as '2<SUP>nd</SUP> ';
  latexdef "2nd" as "2^\mathrm{nd}";
htmldef "supp" as ' supp ';
  althtmldef "supp" as ' supp ';
  latexdef "supp" as "\mathrm{supp}";
htmldef "tpos" as "tpos ";
  althtmldef "tpos" as 'tpos ';
  latexdef "tpos" as "\mathrm{tpos}";
htmldef "curry" as "curry ";
  althtmldef "curry" as 'curry ';
  latexdef "curry" as "\mathrm{curry}";
htmldef "uncurry" as "uncurry ";
  althtmldef "uncurry" as 'uncurry ';
  latexdef "uncurry" as "\mathrm{uncurry}";
htmldef "[C.]" as
    " [<IMG SRC='subsetneq.gif' WIDTH=12 HEIGHT=19 ALT=' C.' TITLE='C.'>] ";
  althtmldef "[C.]" as " [<B>&#x228a;</B>] ";
  latexdef "[C.]" as "\mathrm{[C.]}";
/*
htmldef "iota" as
    "<IMG SRC='iota.gif' WIDTH=6 HEIGHT=19 ALT=' iota' TITLE='iota'>";
  althtmldef "iota" as '<FONT SIZE="+1">&iota;</FONT>';
  latexdef "iota" as "\iota";
*/
/* 30-Nov-2013 changed to rotated iota */
htmldef "iota" as
    "<IMG SRC='riota.gif' WIDTH=6 HEIGHT=19 ALT=' iota' TITLE='iota'>";
  althtmldef "iota" as '&#8489;';
  latexdef "iota" as "\text{\riota}";
htmldef "Smo" as
    "<IMG SRC='_smo.gif' WIDTH=27 HEIGHT=19 ALT=' Smo' TITLE='Smo'> ";
  althtmldef "Smo" as "Smo ";
  latexdef "Smo" as "\mathrm{Smo}";
htmldef "|_|" as ' &#x2294; ';
  althtmldef "|_|" as ' &#x2294; ';
  latexdef "|_|" as "\sqcup";
htmldef "inl" as "inl";
  althtmldef "inl" as "inl";
  latexdef "inl" as "\mathrm{inl}";
htmldef "inr" as "inr";
  althtmldef "inr" as "inr";
  latexdef "inr" as "\mathrm{inr}";
htmldef "recs" as "recs";
  althtmldef "recs" as "recs";
  latexdef "recs" as "\mathrm{recs}";
htmldef "rec" as
    "<IMG SRC='_rec.gif' WIDTH=21 HEIGHT=19 ALT=' rec' TITLE='rec'>";
  althtmldef "rec" as 'rec';
  latexdef "rec" as "\mathrm{rec}";
htmldef "seqom" as "seqom ";
  althtmldef "seqom" as "seq<SUB>&#x3C9;</SUB>";  /* upright lowercase omega */
  latexdef "seqom" as "\operatorname{seq_\omega}";
htmldef "1o" as "<IMG SRC='_1o.gif' WIDTH=13 HEIGHT=19 ALT=' 1o' TITLE='1o'>";
  althtmldef "1o" as '1<SUB>o</SUB>';
  latexdef "1o" as "1_\mathrm{o}";
htmldef "2o" as "<IMG SRC='_2o.gif' WIDTH=14 HEIGHT=19 ALT=' 2o' TITLE='2o'>";
  althtmldef "2o" as '2<SUB>o</SUB>';
  latexdef "2o" as "2_\mathrm{o}";
htmldef "3o" as "<IMG SRC='_3o.gif' WIDTH=14 HEIGHT=19 ALT=' 3o' TITLE='3o'>";
  althtmldef "3o" as "3<SUB>o</SUB>";
  latexdef "3o" as "3_\mathrm{o}";
htmldef "4o" as "<IMG SRC='_4o.gif' WIDTH=15 HEIGHT=19 ALT=' 4o' TITLE='4o'>";
  althtmldef "4o" as "4<SUB>o</SUB>";
  latexdef "4o" as "4_\mathrm{o}";
htmldef "+o" as
    " <IMG SRC='_plo.gif' WIDTH=18 HEIGHT=19 ALT=' +o' TITLE='+o'> ";
  althtmldef "+o" as ' +<SUB>o</SUB> ';
  latexdef "+o" as "+_\mathrm{o}";
htmldef ".o" as
    " <IMG SRC='_cdo.gif' WIDTH=10 HEIGHT=19 ALT=' .o' TITLE='.o'> ";
  althtmldef ".o" as ' &middot;<SUB>o</SUB> ';
  latexdef ".o" as "\cdot_\mathrm{o}";
htmldef "^o" as
    " <IMG SRC='_hato.gif' WIDTH=11 HEIGHT=19 ALT=' ^o' TITLE='^o'> ";
  althtmldef "^o" as ' &uarr;<SUB>o</SUB> ';
  latexdef "^o" as "\uparrow_\mathrm{o}";
htmldef "Er" as
    " <IMG SRC='_er.gif' WIDTH=16 HEIGHT=19 ALT=' Er' TITLE='Er'> ";
  althtmldef "Er" as ' Er ';
  latexdef "Er" as "\mathrel{Er}";
htmldef "/." as
    "<IMG SRC='diagup.gif' WIDTH=14 HEIGHT=19 ALT=' /.' TITLE='/.'>";
  althtmldef "/." as ' <B>/</B> ';
  latexdef "/." as "\pmb{\diagup}";
htmldef "^m" as
    " <IMG SRC='_hatm.gif' WIDTH=15 HEIGHT=19 ALT=' ^m' TITLE='^m'> ";
  althtmldef "^m" as ' &uarr;<SUB>m</SUB> ';
  latexdef "^m" as "\uparrow_\mathrm{m}";
htmldef "^pm" as
    " <IMG SRC='_hatpm.gif' WIDTH=21 HEIGHT=19 ALT=' ^pm' TITLE='^pm'> ";
  althtmldef "^pm" as ' &uarr;<SUB>pm</SUB> ';
  latexdef "^pm" as "\uparrow_\mathrm{pm}";
htmldef "X_" as
    "<IMG SRC='_bigtimes.gif' WIDTH=11 HEIGHT=19 ALT=' X_' TITLE='X_'>";
  althtmldef "X_" as '<FONT SIZE="+1">X</FONT>';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "X_" as "\pmb{\bigtimes}";
htmldef "~~" as
    " <IMG SRC='approx.gif' WIDTH=13 HEIGHT=19 ALT=' ~~' TITLE='~~'> ";
  althtmldef "~~" as ' &#8776; '; /* &ap; */
  latexdef "~~" as "\approx";
htmldef "~<_" as
   " <IMG SRC='preccurlyeq.gif' WIDTH=11 HEIGHT=19 " +
    "ALT=' ~&lt;_' TITLE='~&lt;_'> ";
  althtmldef "~<_" as ' &#8828; '; /* &prcue; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~<_" as "\preccurlyeq";
htmldef "~<" as
    " <IMG SRC='prec.gif' WIDTH=11 HEIGHT=19 ALT=' ~&lt;' TITLE='~&lt;'> ";
  althtmldef "~<" as ' &#8826; '; /* &pr; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~<" as "\prec";
htmldef "Fin" as
    "<IMG SRC='_fin.gif' WIDTH=21 HEIGHT=19 ALT=' Fin' TITLE='Fin'>";
  althtmldef "Fin" as 'Fin';
  latexdef "Fin" as "\mathrm{Fin}";
htmldef "finSupp" as ' finSupp ';
  althtmldef "finSupp" as ' finSupp ';
  latexdef "finSupp" as "\mathrm{finSupp}";
htmldef "Undef" as
    "<IMG SRC='_undef.gif' WIDTH=39 HEIGHT=19 ALT=' Undef' TITLE='Undef'>";
  althtmldef "Undef" as "Undef";
  latexdef "Undef" as "\mathrm{Undef}";
htmldef "iota_" as
    "<IMG SRC='_riotabar.gif' WIDTH=6 HEIGHT=19 ALT=' iota_' TITLE='iota_'>";
  althtmldef "iota_" as '<U>&#8489;</U>';
  latexdef "iota_" as "\underline{\text\riota}";
htmldef "fi" as
    "<IMG SRC='_fi.gif' WIDTH=10 HEIGHT=19 ALT=' fi' TITLE='fi'>";
  althtmldef "fi" as "fi";
  latexdef "fi" as "\mathrm{fi}";
htmldef "sup" as
    "<IMG SRC='_sup.gif' WIDTH=22 HEIGHT=19 ALT=' sup' TITLE='sup'>";
  althtmldef "sup" as 'sup';
  latexdef "sup" as "\operatorname{sup}";
htmldef "inf" as 'inf';
  althtmldef "inf" as 'inf';
  latexdef "inf" as "\operatorname{inf}";
htmldef "OrdIso" as "OrdIso";
  althtmldef "OrdIso" as 'OrdIso';
  latexdef "OrdIso" as "\mathrm{OrdIso}";
/* the standard symbol for this is \aleph, but that collides */
htmldef "har" as "har";
  althtmldef "har" as "har";
  latexdef "har" as "\mathrm{har}";
htmldef "~<_*" as " <IMG SRC='preccurlyeq.gif' WIDTH=11 HEIGHT=19 " +
   "ALT=' ~&lt;_' TITLE='~&lt;_'><SUP>*</SUP> ";
  althtmldef "~<_*" as ' &#8828;<SUP>*</SUP> ';
  /* &prcue; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~<_*" as "\preccurlyeq^*";
htmldef "CNF" as " CNF ";
  /* surrounding spaces since it is often infixed */
  althtmldef "CNF" as " CNF ";
  latexdef "CNF" as "\mathrm{CNF}";
htmldef "TC" as
    "<IMG SRC='_tc.gif' WIDTH=20 HEIGHT=19 ALT=' TC' TITLE='TC'>";
  althtmldef "TC" as "TC";
  latexdef "TC" as "\mathrm{TC}";
htmldef "R1" as "<IMG SRC='_r1.gif' WIDTH=15 HEIGHT=19 ALT=' R1' TITLE='R1'>";
  althtmldef "R1" as '&#x1D445;<SUB>1</SUB>';
  latexdef "R1" as "R_1";
htmldef "rank" as
    "<IMG SRC='_rank.gif' WIDTH=30 HEIGHT=19 ALT=' rank' TITLE='rank'>";
  althtmldef "rank" as 'rank';
  latexdef "rank" as "\mathrm{rank}";
htmldef "Scott" as "Scott ";
  althtmldef "Scott" as "Scott ";
  latexdef "Scott" as "\mathrm{Scott}";
htmldef "card" as
    "<IMG SRC='_card.gif' WIDTH=30 HEIGHT=19 ALT=' card' TITLE='card'>";
  althtmldef "card" as 'card';
  latexdef "card" as "\mathrm{card}";
htmldef "aleph" as
    "<IMG SRC='varaleph.gif' WIDTH=12 HEIGHT=19 ALT=' aleph' TITLE='aleph'>";
  althtmldef "aleph" as '&#8501;'; /* &aleph; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "aleph" as "\aleph";
htmldef "cf" as
    "<IMG SRC='_cofin.gif' WIDTH=14 HEIGHT=19 ALT=' cf' TITLE='cf'>";
  althtmldef "cf" as 'cf';
  latexdef "cf" as "\mathrm{cf}";
htmldef "AC_" as '<U>AC</U> ';
  althtmldef "AC_" as '<U>AC</U> ';
  latexdef "AC_" as "\underline{\mathrm{AC}}";
htmldef "CHOICE" as "<SMALL>CHOICE</SMALL>";
  althtmldef "CHOICE" as "<SMALL>CHOICE</SMALL>";
  latexdef "CHOICE" as "\mathrm{CHOICE}";
htmldef "Fin1a" as "Fin<SUP>Ia</SUP>";
  althtmldef "Fin1a" as "Fin<SUP>Ia</SUP>";
  latexdef "Fin1a" as "\mathrm{Fin1a}";
htmldef "Fin2" as "Fin<SUP>II</SUP>";
  althtmldef "Fin2" as "Fin<SUP>II</SUP>";
  latexdef "Fin2" as "\mathrm{Fin2}";
htmldef "Fin3" as "Fin<SUP>III</SUP>";
  althtmldef "Fin3" as "Fin<SUP>III</SUP>";
  latexdef "Fin3" as "\mathrm{Fin3}";
htmldef "Fin4" as "Fin<SUP>IV</SUP>";
  althtmldef "Fin4" as "Fin<SUP>IV</SUP>";
  latexdef "Fin4" as "\mathrm{Fin4}";
htmldef "Fin5" as "Fin<SUP>V</SUP>";
  althtmldef "Fin5" as "Fin<SUP>V</SUP>";
  latexdef "Fin5" as "\mathrm{Fin5}";
htmldef "Fin6" as "Fin<SUP>VI</SUP>";
  althtmldef "Fin6" as "Fin<SUP>VI</SUP>";
  latexdef "Fin6" as "\mathrm{Fin6}";
htmldef "Fin7" as "Fin<SUP>VII</SUP>";
  althtmldef "Fin7" as "Fin<SUP>VII</SUP>";
  latexdef "Fin7" as "\mathrm{Fin7}";
htmldef "GCH" as "GCH";
  althtmldef "GCH" as "GCH";
  latexdef "GCH" as "\mathrm{GCH}";
htmldef "WUni" as "WUni";
  althtmldef "WUni" as "WUni";
  latexdef "WUni" as "\mathrm{WUni}";
htmldef "wUniCl" as "wUniCl";
  althtmldef "wUniCl" as "wUniCl";
  latexdef "wUniCl" as "\mathrm{wUniCl}";
htmldef "InaccW" as
    "<IMG SRC='_inacc.gif' WIDTH=34 HEIGHT=19 ALT=' Inacc' TITLE='Inacc'>" +
    "<IMG SRC='subw.gif' WIDTH=7 HEIGHT=19 ALT='W' TITLE='W'>";
  althtmldef "InaccW" as "Inacc<SUB>w</SUB>";
  latexdef "InaccW" as "\mathrm{Inacc}_w";
htmldef "Inacc" as
    "<IMG SRC='_inacc.gif' WIDTH=34 HEIGHT=19 ALT=' Inacc' TITLE='Inacc'>";
  althtmldef "Inacc" as "Inacc";
  latexdef "Inacc" as "\mathrm{Inacc}";
htmldef "Tarski" as
    "<IMG SRC='_tarski.gif' WIDTH=40 HEIGHT=19 ALT=' Tarski' TITLE='Tarski'>";
  althtmldef "Tarski" as "Tarski";
  latexdef "Tarski" as "\mathrm{Tarski}";
htmldef "Univ" as
    "<IMG SRC='_univ.gif' WIDTH=30 HEIGHT=19 ALT=' Univ' TITLE='Univ'>";
  althtmldef "Univ" as "Univ";
  latexdef "Univ" as "\mathrm{Univ}";
htmldef "tarskiMap" as "<IMG SRC='_tarskimap.gif' WIDTH=66 HEIGHT=19 " +
    "ALT=' tarskiMap' TITLE='tarskiMap'>";
  althtmldef "tarskiMap" as "tarskiMap";
  latexdef "tarskiMap" as "\mathrm{tarskiMap}";
htmldef "N." as "<IMG SRC='caln.gif' WIDTH=17 HEIGHT=19 ALT=' N.' TITLE='N.'>";
  althtmldef "N." as '<I><B>N</B></I>';
  latexdef "N." as "\mathcal{N}";
htmldef "+N" as
    " <IMG SRC='_pln.gif' WIDTH=22 HEIGHT=19 ALT=' +N' TITLE='+N'> ";
  althtmldef "+N" as ' +<I><SUB><B>N</B></SUB></I> ';
  latexdef "+N" as "+_\mathcal{N}";
htmldef ".N" as
    " <IMG SRC='_cdn.gif' WIDTH=14 HEIGHT=19 ALT=' .N' TITLE='.N'> ";
  althtmldef ".N" as ' &middot;<I><SUB><B>N</B></SUB></I> ';
  latexdef ".N" as "\cdot_\mathcal{N}";
htmldef "<N" as
    " <IMG SRC='_ltn.gif' WIDTH=21 HEIGHT=19 ALT=' &lt;N' TITLE='&lt;N'> ";
  althtmldef "<N" as ' &lt;<I><SUB><B>N</B></SUB></I> ';
  latexdef "<N" as "<_\mathcal{N}";
htmldef "+pQ" as
    " <IMG SRC='_plpq.gif' WIDTH=28 HEIGHT=19 ALT=' +pQ' TITLE='+pQ'> ";
  althtmldef "+pQ" as ' +<I><SUB>p<B>Q</B></SUB></I> ';
  latexdef "+pQ" as "+_{p\mathcal{Q}}";
htmldef ".pQ" as
    " <IMG SRC='_cdpq.gif' WIDTH=19 HEIGHT=19 ALT=' .pQ' TITLE='.pQ'> ";
  althtmldef ".pQ" as ' &middot;<I><SUB>p<B>Q</B></SUB></I> ';
  latexdef ".pQ" as "\cdot_{p\mathcal{Q}}";
htmldef "<pQ" as
    " <IMG SRC='_ltpq.gif' WIDTH=27 HEIGHT=19 ALT=' &lt;pQ' TITLE='&lt;pQ'> ";
  althtmldef "<pQ" as ' &lt;<I><SUB>p<B>Q</B></SUB></I> ';
  latexdef "<pQ" as "<_{p\mathcal{Q}}";
htmldef "~Q" as
    " <IMG SRC='_simq.gif' WIDTH=21 HEIGHT=19 ALT=' ~Q' TITLE='~Q'> ";
  althtmldef "~Q" as ' ~<I><SUB><B>Q</B></SUB></I> ';
  latexdef "~Q" as "\sim_\mathcal{Q}";
htmldef "Q." as "<IMG SRC='calq.gif' WIDTH=12 HEIGHT=19 ALT=' Q.' TITLE='Q.'>";
  althtmldef "Q." as '<I><B>Q</B></I>';
  latexdef "Q." as "\mathcal{Q}";
htmldef "1Q" as "<IMG SRC='_1q.gif' WIDTH=16 HEIGHT=19 ALT=' 1Q' TITLE='1Q'>";
  althtmldef "1Q" as '1<I><SUB><B>Q</B></SUB></I>';
  latexdef "1Q" as "1_\mathcal{Q}";
htmldef "/Q" as "<IMG SRC='_erq.gif' WIDTH=17 HEIGHT=19 ALT=' /Q' TITLE='/Q'>";
  althtmldef "/Q" as '[<I><B>Q</B></I>]';
  latexdef "/Q" as "[\mathcal{Q}]";
htmldef "+Q" as
    " <IMG SRC='_plq.gif' WIDTH=21 HEIGHT=19 ALT=' +Q' TITLE='+Q'> ";
  althtmldef "+Q" as ' +<I><SUB><B>Q</B></SUB></I> ';
  latexdef "+Q" as "+_\mathcal{Q}";
htmldef ".Q" as
    " <IMG SRC='_cdq.gif' WIDTH=13 HEIGHT=19 ALT=' .Q' TITLE='.Q'> ";
  althtmldef ".Q" as ' &middot;<I><SUB><B>Q</B></SUB></I> ';
  latexdef ".Q" as "\cdot_\mathcal{Q}";
htmldef "*Q" as
    "<IMG SRC='_astq.gif' WIDTH=16 HEIGHT=19 ALT=' *Q' TITLE='*Q'>";
  althtmldef "*Q" as '*<I><SUB><B>Q</B></SUB></I>';
  latexdef "*Q" as "\ast_\mathcal{Q}";
htmldef "<Q" as
    " <IMG SRC='_ltq.gif' WIDTH=20 HEIGHT=19 ALT=' &lt;Q' TITLE='&lt;Q'> ";
  althtmldef "<Q" as ' &lt;<I><SUB><B>Q</B></SUB></I> ';
  latexdef "<Q" as "<_\mathcal{Q}";
htmldef "P." as "<IMG SRC='calp.gif' WIDTH=13 HEIGHT=19 ALT=' P.' TITLE='P.'>";
  althtmldef "P." as '<I><B>P</B></I>';
  latexdef "P." as "\mathcal{P}";
htmldef "1P" as "<IMG SRC='_1p.gif' WIDTH=15 HEIGHT=19 ALT=' 1P' TITLE='1P'>";
  althtmldef "1P" as '1<I><SUB><B>P</B></SUB></I>';
  latexdef "1P" as "1_\mathcal{P}";
htmldef "+P." as
    " <IMG SRC='_plp.gif' WIDTH=22 HEIGHT=19 ALT=' +P.' TITLE='+P.'> ";
  althtmldef "+P." as ' +<I><SUB><B>P</B></SUB></I> ';
  latexdef "+P." as "+_\mathcal{P}";
htmldef ".P." as
    " <IMG SRC='_cdp.gif' WIDTH=13 HEIGHT=19 ALT=' .P.' TITLE='.P.'> ";
  althtmldef ".P." as ' &middot;<I><SUB><B>P</B></SUB></I> ';
  latexdef ".P." as "\cdot_\mathcal{P}";
htmldef "<P" as
    " <IMG SRC='_ltp.gif' WIDTH=19 HEIGHT=19 ALT=' &lt;P' TITLE='&lt;P'> ";
  althtmldef "<P" as '&lt;<I><SUB><B>P</B></SUB></I> ';
  latexdef "<P" as "<_\mathcal{P}";
htmldef "~R" as
    " <IMG SRC='_simr.gif' WIDTH=23 HEIGHT=19 ALT=' ~R' TITLE='~R'> ";
  althtmldef "~R" as ' ~<I><SUB><B>R</B></SUB></I> ';
  latexdef "~R" as "\sim_\mathcal{R}";
htmldef "R." as "<IMG SRC='calr.gif' WIDTH=15 HEIGHT=19 ALT=' R.' TITLE='R.'>";
  althtmldef "R." as '<I><B>R</B></I>';
  latexdef "R." as "\mathcal{R}";
htmldef "0R" as "<IMG SRC='_0r.gif' WIDTH=18 HEIGHT=19 ALT=' 0R' TITLE='0R'>";
  althtmldef "0R" as '0<I><SUB><B>R</B></SUB></I>';
  latexdef "0R" as "0_\mathcal{R}";
htmldef "1R" as "<IMG SRC='_1cr.gif' WIDTH=16 HEIGHT=19 ALT=' 1R' TITLE='1R'>";
  althtmldef "1R" as '1<I><SUB><B>R</B></SUB></I>';
  latexdef "1R" as "1_\mathcal{R}";
htmldef "-1R" as
    "<IMG SRC='_m1r.gif' WIDTH=22 HEIGHT=19 ALT=' -1R' TITLE='-1R'>";
  althtmldef "-1R" as '-1<I><SUB><B>R</B></SUB></I>';
  latexdef "-1R" as "-1_\mathcal{R}";
htmldef "+R" as
    " <IMG SRC='_plr.gif' WIDTH=23 HEIGHT=19 ALT=' +R' TITLE='+R'> ";
  althtmldef "+R" as ' +<I><SUB><B>R</B></SUB></I> ';
  latexdef "+R" as "+_\mathcal{R}";
htmldef ".R" as
    " <IMG SRC='_cdcr.gif' WIDTH=14 HEIGHT=19 ALT=' .R' TITLE='.R'> ";
  althtmldef ".R" as ' &middot;<I><SUB><B>R</B></SUB></I> ';
  latexdef ".R" as "\cdot_\mathcal{R}";
htmldef "<R" as
    " <IMG SRC='_ltr.gif' WIDTH=20 HEIGHT=19 ALT=' &lt;R' TITLE='&lt;R'> ";
  althtmldef "<R" as ' &lt;<I><SUB><B>R</B></SUB></I> ';
  latexdef "<R" as "<_\mathcal{R}";
htmldef "<RR" as
    " <IMG SRC='_ltbbr.gif' WIDTH=20 HEIGHT=19 ALT=' &lt;RR' TITLE='&lt;RR'> ";
  althtmldef "<RR" as ' &lt;<SUB>&#8477;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "<RR" as "<_\mathbb{R}";
htmldef "CC" as "<IMG SRC='bbc.gif' WIDTH=12 HEIGHT=19 ALT=' CC' TITLE='CC'>";
  althtmldef "CC" as '&#8450;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "CC" as "\mathbb{C}";
htmldef "RR" as "<IMG SRC='bbr.gif' WIDTH=13 HEIGHT=19 ALT=' RR' TITLE='RR'>";
  althtmldef "RR" as '&#8477;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "RR" as "\mathbb{R}";
    /*latexdef "" as "_{10}";*/
    /*latexdef "" as "";*/
    /* suppress base 10 suffix */
htmldef "0" as "<IMG SRC='0.gif' WIDTH=8 HEIGHT=19 ALT=' 0' TITLE='0'>";
  althtmldef "0" as '0';
  latexdef "0" as "0";
htmldef "1" as "<IMG SRC='1.gif' WIDTH=7 HEIGHT=19 ALT=' 1' TITLE='1'>";
  althtmldef "1" as '1';
  latexdef "1" as "1";
htmldef "_i" as "<IMG SRC='rmi.gif' WIDTH=4 HEIGHT=19 ALT=' _i' TITLE='_i'>";
  althtmldef "_i" as 'i';
  latexdef "_i" as "\mathrm{i}";
htmldef "+" as " <IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'> ";
  althtmldef "+" as ' + ';
  latexdef "+" as "+";
htmldef "x." as
    " <IMG SRC='cdot.gif' WIDTH=4 HEIGHT=19 ALT=' x.' TITLE='x.'> ";
  althtmldef "x." as ' &middot; '; /* unicode: &#xb7; */
  latexdef "x." as "\cdot";
htmldef "<_" as
    " <IMG SRC='le.gif' WIDTH=11 HEIGHT=19 ALT=' &lt;_' TITLE='&lt;_'> ";
  althtmldef "<_" as ' &le; ';
  latexdef "<_" as "\le";
htmldef "+oo" as " <IMG SRC='_pinf.gif' WIDTH=29 HEIGHT=19 ALT='+oo' " +
    "TITLE='+oo'>";
  althtmldef "+oo" as '+&infin;';
  latexdef "+oo" as "+\infty";
htmldef "-oo" as " <IMG SRC='_minf.gif' WIDTH=24 HEIGHT=19 ALT='-oo' " +
    "TITLE='-oo'>";
  althtmldef "-oo" as '-&infin;';
  latexdef "-oo" as "-\infty";
htmldef "RR*" as "<IMG SRC='_bbrast.gif' WIDTH=18 HEIGHT=19 ALT=' RR*' " +
    "TITLE='RR*'>";
  althtmldef "RR*" as '&#8477;<SUP>*</SUP>';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "RR*" as "\mathbb{R}^*";
htmldef "<" as
    " <IMG SRC='lt.gif' WIDTH=11 HEIGHT=19 ALT=' &lt;' TITLE='&lt;'> ";
  althtmldef "<" as ' &lt; ';
  latexdef "<" as "<";
htmldef "-" as
    " <IMG SRC='minus.gif' WIDTH=11 HEIGHT=19 ALT=' -' TITLE='-'> ";
  althtmldef "-" as ' &minus; ';
  latexdef "-" as "-";
htmldef "-u" as
    "<IMG SRC='shortminus.gif' WIDTH=8 HEIGHT=19 ALT=' -u' TITLE='-u'>";
    /* use standard minus sign */
  althtmldef "-u" as '-';
  latexdef "-u" as "\textrm{-}"; /* short minus */
    /*latexdef "-u" as "-_u";*/
htmldef "_Ind" as "&#x1D7ED;";
  althtmldef "_Ind" as "&#x1D7ED;";
  latexdef "_Ind" as "\pmb{1}";
htmldef "NN" as "<IMG SRC='bbn.gif' WIDTH=12 HEIGHT=19 ALT=' NN' TITLE='NN'>";
  althtmldef "NN" as '&#8469;'; /* &Nopf; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "NN" as "\mathbb{N}";
htmldef "NN0" as
    "<IMG SRC='_bbn0.gif' WIDTH=19 HEIGHT=19 ALT=' NN0' TITLE='NN0'>";
  althtmldef "NN0" as '&#8469;<SUB>0</SUB>';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "NN0" as "\mathbb{N}_0";
htmldef "NN0*" as 'NN0*';
  althtmldef "NN0*" as '&#8469;<SUB>0</SUB><SUP>*</SUP>';
  latexdef "NN0*" as "\mathbb{N}_0^*";
htmldef "ZZ" as "<IMG SRC='bbz.gif' WIDTH=11 HEIGHT=19 ALT=' ZZ' TITLE='ZZ'>";
  althtmldef "ZZ" as '&#8484;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "ZZ" as "\mathbb{Z}";
htmldef "QQ" as "<IMG SRC='bbq.gif' WIDTH=13 HEIGHT=19 ALT=' QQ' TITLE='QQ'>";
  althtmldef "QQ" as '&#8474;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "QQ" as "\mathbb{Q}";
htmldef "RR+" as "<IMG SRC='_bbrplus.gif' WIDTH=20 HEIGHT=19 ALT=' RR+' " +
    "TITLE='RR+'>";
  althtmldef "RR+" as '&#8477;<SUP>+</SUP>';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "RR+" as "\mathbb{R}^+";
htmldef "2" as "<IMG SRC='2.gif' WIDTH=8 HEIGHT=19 ALT=' 2' TITLE='2'>";
  althtmldef "2" as '2';
  latexdef "2" as "2";
htmldef "3" as "<IMG SRC='3.gif' WIDTH=8 HEIGHT=19 ALT=' 3' TITLE='3'>";
  althtmldef "3" as '3';
  latexdef "3" as "3";
htmldef "4" as "<IMG SRC='4.gif' WIDTH=9 HEIGHT=19 ALT=' 4' TITLE='4'>";
  althtmldef "4" as '4';
  latexdef "4" as "4";
htmldef "5" as "<IMG SRC='5.gif' WIDTH=8 HEIGHT=19 ALT=' 5' TITLE='5'>";
  althtmldef "5" as '5';
  latexdef "5" as "5";
htmldef "6" as "<IMG SRC='6.gif' WIDTH=8 HEIGHT=19 ALT=' 6' TITLE='6'>";
  althtmldef "6" as '6';
  latexdef "6" as "6";
htmldef "7" as "<IMG SRC='7.gif' WIDTH=9 HEIGHT=19 ALT=' 7' TITLE='7'>";
  althtmldef "7" as '7';
  latexdef "7" as "7";
htmldef "8" as "<IMG SRC='8.gif' WIDTH=8 HEIGHT=19 ALT=' 8' TITLE='8'>";
  althtmldef "8" as '8';
  latexdef "8" as "8";
htmldef "9" as "<IMG SRC='9.gif' WIDTH=8 HEIGHT=19 ALT=' 9' TITLE='9'>";
  althtmldef "9" as '9';
  latexdef "9" as "9";
htmldef ";" as '<FONT COLOR="#808080">;</FONT>';
  althtmldef ";" as '<SPAN CLASS=hidden STYLE="color:gray">;</SPAN>';
  latexdef ";" as ";";
htmldef "ZZ>=" as "<IMG SRC='_bbzge.gif' WIDTH=20 HEIGHT=19 " +
    "ALT=' ZZ&gt;=' TITLE='ZZ&gt;='>";
  althtmldef "ZZ>=" as "&#8484;<SUB>&ge;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "ZZ>=" as "\mathbb{Z}_\ge";
htmldef "-e" as " <IMG SRC='shortminus.gif' WIDTH=8 HEIGHT=19 ALT=' -' " +
    "TITLE='-'><IMG SRC='sube.gif' WIDTH=6 HEIGHT=19 ALT='e' TITLE='e'>";
  althtmldef "-e" as "-<SUB>&#x1D452;</SUB>";
  latexdef "-e" as "\textrm{-}_e";
htmldef "+e" as "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>" +
    "<IMG SRC='sube.gif' WIDTH=6 HEIGHT=19 ALT='e' TITLE='e'>";
  althtmldef "+e" as " +<SUB>&#x1D452;</SUB> ";
  latexdef "+e" as "+_e";
htmldef "*e" as "<IMG SRC='cdot.gif' WIDTH=4 HEIGHT=19 ALT=' x' TITLE='x'>" +
    "<IMG SRC='sube.gif' WIDTH=6 HEIGHT=19 ALT='e' TITLE='e'>";
  althtmldef "*e" as  " &middot;<SUB>e</SUB> ";
  latexdef "*e" as "\cdot_e";
htmldef "(,)" as
    "<IMG SRC='_ioo.gif' WIDTH=13 HEIGHT=19 ALT=' (,)' TITLE='(,)'>";
  althtmldef "(,)" as "(,)";
  latexdef "(,)" as "(,)";
htmldef "(,]" as
    "<IMG SRC='_ioc.gif' WIDTH=12 HEIGHT=19 ALT=' (,]' TITLE='(,]'>";
  althtmldef "(,]" as "(,]";
  latexdef "(,]" as "(,]";
htmldef "[,)" as
    "<IMG SRC='_ico.gif' WIDTH=13 HEIGHT=19 ALT=' [,)' TITLE='[,)'>";
  althtmldef "[,)" as "[,)";
  latexdef "[,)" as "[,)";
htmldef "[,]" as
    "<IMG SRC='_icc.gif' WIDTH=12 HEIGHT=19 ALT=' [,]' TITLE='[,]'>";
  althtmldef "[,]" as "[,]";
  latexdef "[,]" as "[,]";
htmldef "..." as "<IMG SRC='ldots.gif' WIDTH=18 HEIGHT=19 " +
    "ALT=' ...' TITLE='...'>";
  althtmldef "..." as "...";
  latexdef "..." as "\ldots";
htmldef "..^" as "..^";
  althtmldef "..^" as "..^";
  latexdef "..^" as "\mathbin{..\hat{\;}}";
/*
htmldef "sgn" as
    "<IMG SRC='sgn.gif' WIDTH=20 HEIGHT=19 ALT=' sgn' TITLE='sgn'>";
*/
htmldef "sgn" as "sgn";
  althtmldef "sgn" as "sgn";
  latexdef "sgn" as "\operatorname{sgn}";
htmldef "|_" as "<IMG SRC='lfloor.gif' WIDTH=6 HEIGHT=19 ALT=' |_' " +
    "TITLE='|_'>";
  althtmldef "|_" as '&#8970;';
  latexdef "|_" as "\lfloor";
/*
htmldef "|^" as
   "<IMG SRC='ceiling.gif' WIDTH=20 HEIGHT=19 ALT=' ceiling' TITLE='ceiling'>";
*/
htmldef "|^" as "&#8968;";
  althtmldef "|^" as "&#8968;";
  latexdef "|^" as "\lceil";
htmldef "mod" as " <IMG SRC='_mod.gif' WIDTH=29 HEIGHT=19 ALT=' mod' " +
    "TITLE='mod'> ";
  althtmldef "mod" as ' mod ';
  latexdef "mod" as "\mathbin{\operatorname{mod}}";
htmldef "==" as " <IMG SRC='equiv.gif' WIDTH=12 HEIGHT=19 ALT=' ==' " +
    "TITLE='=='> ";
  althtmldef "==" as "&equiv;"; /* 2263 */
  latexdef "==" as "\equiv";
htmldef "seq" as " <IMG SRC='_seq.gif' WIDTH=22 HEIGHT=19 ALT=' seq' " +
    "TITLE='seq'>";
  althtmldef "seq" as 'seq';
  latexdef "seq" as "\mathrm{seq}";
/*
htmldef "seq1" as " <IMG SRC='_seq1.gif' WIDTH=26 HEIGHT=19 ALT=' seq1' " +
    "TITLE='seq1'> ";
  althtmldef "seq1" as 'seq<SUB>1</SUB>';
  latexdef "seq1" as "\mathrm{seq}_1";
htmldef "seqz" as
    " <IMG SRC='_seq.gif' WIDTH=22 HEIGHT=19 ALT=' seq' TITLE='seq'>" +
    "<IMG SRC='__subbbz.gif' WIDTH=8 HEIGHT=19 ALT='z' TITLE='z'> ";
  althtmldef "seqz" as 'seq<SUB><FONT FACE=sans-serif>&#8484;</FONT></SUB>';
  latexdef "seqz" as "\mathrm{seq}_\mathbb{Z}";
htmldef "seq0" as " <IMG SRC='_seq0.gif' WIDTH=27 HEIGHT=19 ALT=' seq0' " +
    "TITLE='seq0'> ";
  althtmldef "seq0" as 'seq<SUB>0</SUB>';
  latexdef "seq0" as "\mathrm{seq}_0";
*/
htmldef "^" as "<IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' ^' TITLE='^'>";
  althtmldef "^" as '&uarr;';
  latexdef "^" as "\uparrow";
htmldef "!" as "<IMG SRC='bang.gif' WIDTH=3 HEIGHT=19 ALT=' !' TITLE='!'>";
  althtmldef "!" as '!';
  latexdef "!" as "{!}";
htmldef "_C" as
    " <IMG SRC='rmcc.gif' WIDTH=10 HEIGHT=19 ALT=' _C' TITLE='_C'> ";
  althtmldef "_C" as 'C';
  latexdef "_C" as "\mathbin{\operatorname{C}}";
htmldef "#" as "&#x266f";
  althtmldef "#" as "&#x266f";
  latexdef "#" as "\sharp";
htmldef "shift" as " <IMG SRC='_shift.gif' WIDTH=30 HEIGHT=19 ALT=' shift' " +
    "TITLE='shift'> ";
  althtmldef "shift" as ' shift ';
  latexdef "shift" as "\mathbin{\operatorname{shift}}";
htmldef "Re" as "<IMG SRC='re.gif' WIDTH=12 HEIGHT=19 ALT=' Re' TITLE='Re'>";
  althtmldef "Re" as '&real;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "Re" as "\Re";
htmldef "Im" as "<IMG SRC='im.gif' WIDTH=12 HEIGHT=19 ALT=' Im' TITLE='Im'>";
  althtmldef "Im" as '&image;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "Im" as "\Im";
htmldef "*" as "<IMG SRC='ast.gif' WIDTH=7 HEIGHT=19 ALT=' *' TITLE='*'>";
  althtmldef "*" as '&lowast;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "*" as "*";
htmldef "sqrt" as
    "<IMG SRC='surd.gif' WIDTH=14 HEIGHT=19 ALT=' sqr' TITLE='sqr'>";
  althtmldef "sqrt" as '&radic;';
  latexdef "sqrt" as "\surd";
htmldef "abs" as
    "<IMG SRC='_abs.gif' WIDTH=22 HEIGHT=19 ALT=' abs' TITLE='abs'>";
  althtmldef "abs" as 'abs';
  latexdef "abs" as "\operatorname{abs}";
htmldef "+-" as
    "<IMG SRC='pm.gif' WIDTH=14 HEIGHT=19 ALT=' pm' TITLE='pm'>";
  althtmldef "+-" as '&plusmn;';
  latexdef "+-" as "\pm";
htmldef "limsup" as
    "<IMG SRC='_limsup.gif' WIDTH=44 HEIGHT=19 ALT=' limsup' TITLE='limsup'>";
  althtmldef "limsup" as 'lim sup';
  latexdef "limsup" as "\limsup";
htmldef "~~>" as " <IMG SRC='rightsquigarrow.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' ~~&gt;' TITLE='~~&gt;'> ";
  althtmldef "~~>" as ' &#8669; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~~>" as '\rightsquigarrow';
htmldef "~~>r" as " <IMG SRC='rightsquigarrow.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' ~~&gt;' TITLE='~~&gt;'><IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 " +
    "ALT=' r' TITLE='r'> ";
  althtmldef "~~>r" as
    ' &#8669;<SUB>&#x1D45F;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~~>r" as '\rightsquigarrow_r';
htmldef "O(1)" as "<IMG SRC='co.gif' WIDTH=12 HEIGHT=19 ALT=' O' TITLE='O'>" +
    "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT='(' TITLE='('>" +
    "<IMG SRC='1.gif' WIDTH=7 HEIGHT=19 ALT='1' TITLE='1'>" +
    "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 ALT=')' TITLE=')'>";
  althtmldef "O(1)" as '&#x1D442;(1)';
  latexdef "O(1)" as "O(1)";
htmldef "<_O(1)" as
    "<IMG SRC='le.gif' WIDTH=11 HEIGHT=19 ALT=' &lt;_' TITLE='&lt;_'>" +
    "<IMG SRC='co.gif' WIDTH=12 HEIGHT=19 ALT='O' TITLE='O'>" +
    "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT='(' TITLE='('>" +
    "<IMG SRC='1.gif' WIDTH=7 HEIGHT=19 ALT='1' TITLE='1'>" +
    "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 ALT=')' TITLE=')'>";
  althtmldef "<_O(1)" as '&le;&#x1D442;(1)';
  latexdef "<_O(1)" as "\le O(1)";
htmldef "sum_" as "<IMG SRC='csigma.gif' WIDTH=11 HEIGHT=19 " +
    "ALT=' sum_' TITLE='sum_'>";
  althtmldef "sum_" as "&Sigma;";
  latexdef "sum_" as "\sum";
htmldef "exp" as
    "<IMG SRC='_exp.gif' WIDTH=24 HEIGHT=19 ALT=' exp' TITLE='exp'>";
  althtmldef "exp" as "exp";
  latexdef "exp" as "\exp";
htmldef "_e" as "<IMG SRC='rme.gif' WIDTH=7 HEIGHT=19 ALT=' _e' TITLE='_e'>";
  althtmldef "_e" as "e";
  latexdef "_e" as "\mathrm{e}";
htmldef "sin" as
    "<IMG SRC='_sin.gif' WIDTH=19 HEIGHT=19 ALT=' sin' TITLE='sin'>";
  althtmldef "sin" as "sin";
  latexdef "sin" as "\sin";
htmldef "cos" as
    "<IMG SRC='_cos.gif' WIDTH=21 HEIGHT=19 ALT=' cos' TITLE='cos'>";
  althtmldef "cos" as "cos";
  latexdef "cos" as "\cos";
htmldef "tan" as
    "<IMG SRC='_tan.gif' WIDTH=22 HEIGHT=19 ALT=' tan' TITLE='tan'>";
  althtmldef "tan" as "tan";
  latexdef "tan" as "\tan";
htmldef "_pi" as "<IMG SRC='pi.gif' WIDTH=10 HEIGHT=19 ALT=' pi' TITLE='pi'>";
  althtmldef "_pi" as "&pi;";  /* was: "&#x1D70B;"; math italic pi */
  latexdef "_pi" as "\mathrm{\pi}";
htmldef "_tau" as
    "<IMG SRC='tau.gif' WIDTH=10 HEIGHT=19 ALT=' tau' TITLE='tau'>";
  althtmldef "_tau" as '&#x3c4;';  /* upright lowercase Greek tau */
  latexdef "_tau" as "\mathrm{\tau}";
htmldef "||" as
    " <IMG SRC='parallel.gif' WIDTH=5 HEIGHT=19 " + "ALT=' ||' TITLE='||'> ";
  althtmldef "||" as ' &#8741; ';
  latexdef "||" as " \parallel ";
htmldef "bits" as "bits";
  althtmldef "bits" as "bits";
  latexdef "bits" as "\text{ bits }";
htmldef "sadd" as " sadd ";
  althtmldef "sadd" as " sadd ";
  latexdef "sadd" as "\text{ sadd }";
htmldef "smul" as " smul ";
  althtmldef "smul" as " smul ";
  latexdef "smul" as "\text{ smul }";
htmldef "gcd" as
    " <IMG SRC='_gcd.gif' WIDTH=23 HEIGHT=19 ALT=' gcd' TITLE='gcd'> ";
  althtmldef "gcd" as " gcd ";
  latexdef "gcd" as "\mathbin{\operatorname{gcd}}";
htmldef "lcm" as " lcm ";
  althtmldef "lcm" as " lcm ";
  latexdef "lcm" as "\mathbin{\operatorname{lcm}}";
htmldef "_lcm" as "<U>lcm</U>";
  althtmldef "_lcm" as "<U>lcm</U>";
  latexdef "_lcm" as "\underline{\mathbin{\operatorname{lcm}}}";
htmldef "Prime" as
    "<IMG SRC='bbp.gif' WIDTH=11 HEIGHT=19 ALT=' Prime' TITLE='Prime'>";
  althtmldef "Prime" as "&#8473;";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "Prime" as "\mathbb{P}";
htmldef "#p" as "#<SUB>p</SUB>";
  althtmldef "#p" as "#<SUB>p</SUB>";
  latexdef "#p" as "\#";
htmldef "odZ" as
    "<IMG SRC='_od.gif' WIDTH=15 HEIGHT=19 ALT=' od' TITLE='od'>" +
    "<IMG SRC='__subbbz.gif' WIDTH=8 HEIGHT=19 ALT='Z' TITLE='Z'>";
  althtmldef "odZ" as "od<SUB>&#8484;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "odZ" as "\mathrm{od}_\mathbb{Z}";
htmldef "phi" as
    "<IMG SRC='phi.gif' WIDTH=10 HEIGHT=19 ALT=' phi' TITLE='phi'>";
  althtmldef "phi" as '&#981;';
  latexdef "phi" as "\phi";
htmldef "pCnt" as
    " <IMG SRC='_pcnt.gif' WIDTH=32 HEIGHT=19 ALT=' pCnt' TITLE='pCnt'> ";
  althtmldef "pCnt" as " pCnt ";
  latexdef "pCnt" as "\mathbin{\operatorname{pCnt}}";
htmldef "Z[i]" as
    "<IMG SRC='bbz.gif' WIDTH=11 HEIGHT=19 ALT=' ZZ' TITLE='ZZ'>" +
    "<IMG SRC='lbrack.gif' WIDTH=5 HEIGHT=19 ALT='[' TITLE='['>" +
    "<IMG SRC='rmi.gif' WIDTH=4 HEIGHT=19 ALT='_i' TITLE='_i'>" +
    "<IMG SRC='rbrack.gif' WIDTH=5 HEIGHT=19 ALT=']' TITLE=']'>";
  althtmldef "Z[i]" as '&#8484;[i]';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "Z[i]" as "\mathbb{Z}[\mathrm{i}]";
htmldef "AP" as "AP";
  althtmldef "AP" as "AP";
  latexdef "AP" as "\mathrm{AP}";
htmldef "MonoAP" as " MonoAP ";
  althtmldef "MonoAP" as " MonoAP ";
  latexdef "MonoAP" as "\mathrm{MonoAP}";
htmldef "PolyAP" as " PolyAP ";
  althtmldef "PolyAP" as " PolyAP ";
  latexdef "PolyAP" as "\mathrm{PolyAP}";
htmldef "Ramsey" as " Ramsey ";
  althtmldef "Ramsey" as " Ramsey ";
  latexdef "Ramsey" as "\mathrm{Ramsey}";
htmldef "Struct" as " Struct ";
  althtmldef "Struct" as " Struct ";
  latexdef "Struct" as "\mathrm{Struct}";
htmldef "ndx" as
    "<IMG SRC='_ndx.gif' WIDTH=24 HEIGHT=19 ALT=' ndx' TITLE='ndx'>";
  althtmldef "ndx" as "ndx";
  latexdef "ndx" as "\mathrm{ndx}";
htmldef "sSet" as " sSet ";
  althtmldef "sSet" as " sSet ";
  latexdef "sSet" as "\mathrm{sSet}";
htmldef "Slot" as "Slot ";
  althtmldef "Slot" as "Slot ";
  latexdef "Slot" as "\mathrm{Slot}";
htmldef "Base" as
    "<IMG SRC='_base.gif' WIDTH=30 HEIGHT=19 ALT=' Base' TITLE='Base'>";
  althtmldef "Base" as "Base";
  latexdef "Base" as "\mathrm{Base}";
htmldef "|`s" as " &#8638;<SUB>s</SUB> ";
    /* 2-Jan-2016 reverted sans-serif */
  althtmldef "|`s" as " &#8638;<SUB>s</SUB> ";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|`s" as "\restriction_s";
htmldef "+g" as
    "<IMG SRC='_plusg.gif' WIDTH=19 HEIGHT=19 ALT=' +g' TITLE='+g'> ";
  althtmldef "+g" as "+<SUB>g</SUB>";
  latexdef "+g" as "+_\mathrm{g}";
htmldef ".r" as "<IMG SRC='_cdr.gif' WIDTH=10 HEIGHT=19 ALT=' .r' TITLE='.r'>";
  althtmldef ".r" as ".<SUB>r</SUB>";
  latexdef ".r" as "._\mathrm{r}";
htmldef "*r" as "<IMG SRC='ast.gif' WIDTH=7 HEIGHT=19 ALT=' *' TITLE='*'>" +
    "<IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 ALT='r' TITLE='r'>";
  althtmldef "*r" as "*<SUB>&#x1D45F;</SUB>";
  latexdef "*r" as "\ast_r";
htmldef "Scalar" as "Scalar";
  althtmldef "Scalar" as "Scalar";
  latexdef "Scalar" as "\mathrm{Scalar}";
htmldef ".s" as "<IMG SRC='_cds.gif' WIDTH=9 HEIGHT=19 ALT=' .s' TITLE='.s'>";
  althtmldef ".s" as ' <B>&middot;</B><SUB>&#x1D460;</SUB> ';
  latexdef ".s" as '\cdot_s';
htmldef ".i" as "<IMG SRC='_cdi.gif' WIDTH=7 HEIGHT=19 ALT=' .i' TITLE='.i'>";
  althtmldef ".i" as '<B>&middot;</B><SUB>&#x1D456;</SUB>';
  latexdef ".i" as '\cdot_i';
htmldef "TopSet" as "TopSet";
  althtmldef "TopSet" as "TopSet";
  latexdef "TopSet" as "\mathrm{TopSet}";
htmldef "le" as
    "<IMG SRC='_rmle.gif' WIDTH=11 HEIGHT=19 ALT=' le' TITLE='le'>";
  althtmldef "le" as "le";
  latexdef "le" as "\mathrm{le}";
htmldef "oc" as "<IMG SRC='_oc.gif' WIDTH=14 HEIGHT=19 ALT=' oc' TITLE='oc'>";
  althtmldef "oc" as "oc";
  latexdef "oc" as "\mathrm{oc}";
htmldef "dist" as
    "<IMG SRC='_dist.gif' WIDTH=24 HEIGHT=19 ALT=' dist' TITLE='dist'>";
  althtmldef "dist" as "dist";
  latexdef "dist" as "\mathrm{dist}";
htmldef "UnifSet" as
    "<IMG SRC='_unif.gif' WIDTH=28 HEIGHT=19 ALT=' UnifSet' TITLE='UnifSet'>";
  althtmldef "UnifSet" as "UnifSet";
  latexdef "UnifSet" as "\mathrm{UnifSet}";
htmldef "Hom" as
    "<IMG SRC='_hom.gif' WIDTH=27 HEIGHT=19 ALT=' Hom' TITLE='Hom'> ";
  althtmldef "Hom" as "Hom ";
  latexdef "Hom" as "\mathrm{Hom}";
htmldef "comp" as "comp";
  althtmldef "comp" as "comp";
  latexdef "comp" as "\operatorname{comp}";
htmldef "|`t" as " &#8638;<SUB>t</SUB> ";
    /* 2-Jan-2016 reverted sans-serif */
  althtmldef "|`t" as " &#8638;<SUB>t</SUB> ";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|`t" as "\restriction_t";
htmldef "TopOpen" as
  "<IMG SRC='_topopen.gif' WIDTH=57 HEIGHT=19 ALT=' TopOpen' TITLE='TopOpen'>";
  althtmldef "TopOpen" as "TopOpen";
  latexdef "TopOpen" as "\mathrm{TopOpen}";
htmldef "topGen" as
    "<IMG SRC='_topgen.gif' WIDTH=47 HEIGHT=19 ALT=' topGen' TITLE='topGen'>";
  althtmldef "topGen" as "topGen";
  latexdef "topGen" as "\mathrm{topGen}";
htmldef "Xt_" as
    "<IMG SRC='_prodt.gif' WIDTH=17 HEIGHT=19 ALT=' Xt_' TITLE='Xt_'>";
  althtmldef "Xt_" as "&prod;<SUB>t</SUB>";
  latexdef "Xt_" as "\prod_t";
htmldef "Xs_" as "<IMG SRC='_bigtimes.gif' WIDTH=11 HEIGHT=19 ALT=' X_' " +
    "TITLE='X_'><sub><i>s</i></sub>";
  althtmldef "Xs_" as
    "<FONT SIZE='+1' FACE=sans-serif>X</FONT><sub><i>s</i></sub>";
  latexdef "Xs_" as "\pmb{\bigtimes}_\text{s}";
htmldef "^s" as " <IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' ^' " +
    "TITLE='^'><sub><i>s</i></sub> ";
  althtmldef "^s" as ' &uarr;<sub><i>s</i></sub> ';
  latexdef "^s" as " \uparrow_s ";
htmldef "ordTop" as "ordTop";
  althtmldef "ordTop" as "ordTop";
  latexdef "ordTop" as "\mathrm{ordTop}";
htmldef "RR*s" as
    "<IMG SRC='_bbrast.gif' WIDTH=18 HEIGHT=19 ALT=' RR*' TITLE='RR*'>" +
    "<IMG SRC='subs.gif' WIDTH=6 HEIGHT=19 ALT='s' TITLE='s'>";
  althtmldef "RR*s" as
    '&#8477;<SUP>*</SUP><SUB>&#x1D460;</SUB>';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "RR*s" as "\mathbb{R}^*_s";
htmldef "0g" as "<IMG SRC='_0g.gif' WIDTH=14 HEIGHT=19 ALT=' 0g' TITLE='0g'>";
  althtmldef "0g" as "0<SUB>g</SUB>";
  latexdef "0g" as "0_\mathrm{g}";
htmldef "gsum" as " <IMG SRC='csigma.gif' WIDTH=11 HEIGHT=19 " +
    "ALT=' gsum' TITLE='gsum'><sub><i>g</i></sub> ";
  althtmldef "gsum" as " &Sigma;<sub><i>g</i></sub> ";
  latexdef "gsum" as "\sum_g";
htmldef '"s' as " <IMG SRC='backquote.gif' WIDTH=7 HEIGHT=19 ALT=' " + '"' +
    "' TITLE='" + '"' + "'><sub><i>s</i></sub> ";
  althtmldef '"s' as ' &ldquo;<sub><i>s</i></sub> ';
  latexdef '"s' as "``_s";
htmldef "/s" as " <IMG SRC='diagup.gif' WIDTH=14 HEIGHT=19 ALT=' /.' " +
    "TITLE='/.'><sub><i>s</i></sub> ";
  althtmldef "/s" as " /<sub><i>s</i></sub> ";
  latexdef "/s" as " \diagup_s ";
htmldef "qTop" as " qTop ";
  althtmldef "qTop" as " qTop ";
  latexdef "qTop" as "\mathrm{qTop}";
htmldef "Xs." as " <IMG SRC='times.gif' WIDTH=9 HEIGHT=19 ALT=' X.' " +
    "TITLE='X.'><sub><i>s</i></sub> ";
  althtmldef "Xs." as ' &times;<sub><i>s</i></sub> ';
  latexdef "Xs." as "\times_s";
htmldef "Cat" as
    "<IMG SRC='_cat.gif' WIDTH=24 HEIGHT=19 ALT=' Cat' TITLE='Cat'>";
  althtmldef "Cat" as "Cat";
  latexdef "Cat" as "\mathrm{Cat}";
htmldef "Id" as "<IMG SRC='_id.gif' WIDTH=12 HEIGHT=19 ALT=' Id' TITLE='Id'>";
  althtmldef "Id" as "Id";
  latexdef "Id" as "\mathrm{Id}";
htmldef "Homf" as
    "<IMG SRC='_hom.gif' WIDTH=27 HEIGHT=19 ALT=' Hom' TITLE='Hom'> " +
    "<sub><i>f</i></sub> ";
  althtmldef "Homf" as "Hom<sub><i>f</i></sub> ";
  latexdef "Homf" as "\mathrm{Hom}_f ";
htmldef "comf" as "comp<sub><i>f</i></sub>";
  althtmldef "comf" as "comp<sub><i>f</i></sub>";
  latexdef "comf" as "\mathrm{comp}_f";
htmldef "oppCat" as "oppCat";
  althtmldef "oppCat" as "oppCat";
  latexdef "oppCat" as "\mathrm{oppCat}";
htmldef "Mono" as "Mono";
  althtmldef "Mono" as "Mono";
  latexdef "Mono" as "\mathrm{Mono}";
htmldef "Epi" as "Epi";
  althtmldef "Epi" as "Epi";
  latexdef "Epi" as "\mathrm{Epi}";
htmldef "Sect" as "Sect";
  althtmldef "Sect" as "Sect";
  latexdef "Sect" as "\mathrm{Sect}";
htmldef "Inv" as "Inv";
  althtmldef "Inv" as "Inv";
  latexdef "Inv" as "\mathrm{Inv}";
htmldef "Iso" as
    " <IMG SRC='_iso.gif' WIDTH=17 HEIGHT=19 ALT=' Iso' TITLE='Iso'> ";
  althtmldef "Iso" as "Iso";
  latexdef "Iso" as "\mathrm{Iso}";
htmldef "~=c" as " <IMG SRC='simeq.gif' WIDTH=26 HEIGHT=19 " +
    "ALT=' ~=c' TITLE='~=c'><SUB>&#x1D450;</SUB> ";
  althtmldef "~=c" as " &#8771;<SUB>&#x1D450;</SUB> ";
  latexdef "~=c" as "\simeq_{c}";
htmldef "C_cat" as
    " <IMG SRC='subseteq.gif' WIDTH=12 HEIGHT=19 ALT=' C_' TITLE='C_'>" +
    "<SUB>cat</SUB> ";
  althtmldef "C_cat" as ' &#8838;<SUB>cat</SUB> '; /* &subE; */
  latexdef "C_cat" as "\subseteq_{cat}";
htmldef "|`cat" as " <IMG SRC='restriction.gif' WIDTH=5 HEIGHT=19 ALT=' |`'" +
    " TITLE='|`'><SUB>cat</SUB> ";
  althtmldef "|`cat" as " &#8638;<SUB>cat</SUB> ";
  latexdef "|`cat" as "\restriction_{cat}";
htmldef "Subcat" as "Subcat";
  althtmldef "Subcat" as "Subcat";
  latexdef "Subcat" as "\mathrm{Subcat}";
htmldef "Func" as
    " <IMG SRC='_func.gif' WIDTH=32 HEIGHT=19 ALT=' Func' TITLE='Func'> ";
  althtmldef "Func" as " Func ";
  latexdef "Func" as "\mathbin{\operatorname{Func}}";
htmldef "idFunc" as "id<sub><i>func</i></sub>";
  althtmldef "idFunc" as "id<sub><i>func</i></sub>";
  latexdef "idFunc" as "\mathrm{id}_{func}";
htmldef "o.func" as
    " <IMG SRC='circ.gif' WIDTH=8 HEIGHT=19 ALT=' o.' TITLE='o.'>" +
    "<sub><i>func</i></sub> ";
  althtmldef "o.func" as ' &#8728;<sub><i>func</i></sub> ';
  latexdef "o.func" as "\circ_{func}";
htmldef "|`f" as " <IMG SRC='restriction.gif' WIDTH=5 HEIGHT=19 ALT=' |`'" +
    " TITLE='|`'><SUB><i>f</i></SUB> ";
  althtmldef "|`f" as " &#8638;<SUB><i>f</i></SUB> ";
  latexdef "|`f" as "\restriction_f";
htmldef "Full" as " Full ";
  althtmldef "Full" as " Full ";
  latexdef "Full" as "\mathrm{Full}";
htmldef "Faith" as " Faith ";
  althtmldef "Faith" as " Faith ";
  latexdef "Faith" as "\mathrm{Faith}";
htmldef "Nat" as " Nat ";
  althtmldef "Nat" as " Nat ";
  latexdef "Nat" as "\mathrm{Nat}";
htmldef "FuncCat" as " FuncCat ";
  althtmldef "FuncCat" as " FuncCat ";
  latexdef "FuncCat" as " \mathrm{FuncCat} ";
htmldef "InitO" as 'InitO';
  althtmldef "InitO" as 'InitO';
  latexdef "InitO" as "\mathrm{InitO}";
htmldef "TermO" as 'TermO';
  althtmldef "TermO" as 'TermO';
  latexdef "TermO" as "\mathrm{TermO}";
htmldef "ZeroO" as 'ZeroO';
  althtmldef "ZeroO" as 'ZeroO';
  latexdef "ZeroO" as "\mathrm{ZeroO}";
htmldef "domA" as
    "<IMG SRC='_dom.gif' WIDTH=26 HEIGHT=19 ALT='dom' TITLE='dom'>" +
    "<IMG SRC='suba.gif' WIDTH=7 HEIGHT=19 ALT='A' TITLE='A'>";
  althtmldef "domA" as 'dom<sub><i>a</i></sub>';
  latexdef "domA" as "\mathrm{dom}_a";
htmldef "codA" as 'cod<sub><i>a</i></sub>';
  althtmldef "codA" as 'cod<sub><i>a</i></sub>';
  latexdef "codA" as "\mathrm{cod}_a";
htmldef "Arrow" as "Nat";
  althtmldef "Arrow" as "Arrow";
  latexdef "Arrow" as "\mathrm{Arrow}";
htmldef "HomA" as 'Hom<sub><i>a</i></sub>';
  althtmldef "HomA" as 'Hom<sub><i>a</i></sub>';
  latexdef "HomA" as "\mathrm{Hom}_a";
htmldef "IdA" as 'Id<sub><i>a</i></sub>';
  althtmldef "IdA" as 'Id<sub><i>a</i></sub>';
  latexdef "IdA" as "\mathrm{Id}_a";
htmldef "compA" as 'comp<sub><i>a</i></sub>';
  althtmldef "compA" as 'comp<sub><i>a</i></sub>';
  latexdef "compA" as "\mathrm{comp}_a";
htmldef "SetCat" as
    "<IMG SRC='_setcat.gif' WIDTH=45 HEIGHT=19 ALT=' SetCat' TITLE='SetCat'>";
  althtmldef "SetCat" as "SetCat";
  latexdef "SetCat" as "\mathrm{SetCat}";
htmldef "CatCat" as "CatCat";
  althtmldef "CatCat" as "CatCat";
  latexdef "CatCat" as "\mathrm{CatCat}";
htmldef "ExtStrCat" as 'ExtStrCat';
  althtmldef "ExtStrCat" as 'ExtStrCat';
  latexdef "ExtStrCat" as "\mathrm{ExtStrCat}";
htmldef "Xc." as " <IMG SRC='times.gif' WIDTH=9 HEIGHT=19 ALT=' X.' " +
    "TITLE='X.'><sub><i>c</i></sub> ";
  althtmldef "Xc." as ' &times;<sub><i>c</i></sub> ';
  latexdef "Xc." as "\times_c";
htmldef "1stF" as
    " <IMG SRC='_1st.gif' WIDTH=15 HEIGHT=19 ALT=' 1st' TITLE='1st'>" +
    "<sub><i>F</i></sub> ";
  althtmldef "1stF" as ' 1<SUP>st</SUP><sub><i>F</i></sub> ';
  latexdef "1stF" as " 1^\mathrm{st}{}_F ";
htmldef "2ndF" as
    " <IMG SRC='_2nd.gif' WIDTH=21 HEIGHT=19 ALT=' 2nd' TITLE='2nd'>" +
    "<sub><i>F</i></sub> ";
  althtmldef "2ndF" as ' 2<SUP>nd</SUP><sub><i>F</i></sub> ';
  latexdef "2ndF" as " 2^\mathrm{nd}{}_F ";
htmldef "pairF" as ' &lang;,&rang;<sub><i>F</i></sub> ';
  althtmldef "pairF" as ' &lang;,&rang;<sub><i>F</i></sub> ';
  latexdef "pairF" as " \langle,\rangle_F ";
htmldef "evalF" as ' eval<sub><i>F</i></sub> ';
  althtmldef "evalF" as ' eval<sub><i>F</i></sub> ';
  latexdef "evalF" as "\mathbin{\operatorname{eval}}_F";
htmldef "curryF" as ' curry<sub><i>F</i></sub> ';
  althtmldef "curryF" as ' curry<sub><i>F</i></sub> ';
  latexdef "curryF" as "\mathrm{curry}_F";
htmldef "uncurryF" as ' uncurry<sub><i>F</i></sub> ';
  althtmldef "uncurryF" as ' uncurry<sub><i>F</i></sub> ';
  latexdef "uncurryF" as "\mathrm{uncurry}_F";
htmldef "DiagFunc" as "&Delta;<sub>func</sub>";
  althtmldef "DiagFunc" as "&Delta;<sub>func</sub>";
  latexdef "DiagFunc" as "\Delta_{func}";
htmldef "HomF" as 'Hom<sub><i>F</i></sub>';
  althtmldef "HomF" as 'Hom<sub><i>F</i></sub>';
  latexdef "HomF" as "\mathrm{Hom}_F";
htmldef "Yon" as "Yon";
  althtmldef "Yon" as "Yon";
  latexdef "Yon" as "\mathrm{Yon}";
htmldef "Proset" as
   " <IMG SRC='_preset.gif' WIDTH=41 HEIGHT=19 ALT=' Proset' TITLE='Proset'> ";
  althtmldef "Proset" as " Proset ";
  latexdef "Proset" as "\mathrm{Proset}";
htmldef "Dirset" as "Dirset";
  althtmldef "Dirset" as "Dirset";
  latexdef "Dirset" as "\mathrm{Dirset}";
htmldef "Poset" as
    "<IMG SRC='_poset.gif' WIDTH=35 HEIGHT=19 ALT=' Poset' TITLE='Poset'>";
  althtmldef "Poset" as "Poset";
  latexdef "Poset" as "\mathrm{Poset}";
htmldef "lt" as
    "<IMG SRC='_rmlt.gif' WIDTH=10 HEIGHT=19 ALT=' lt' TITLE='lt'>";
  althtmldef "lt" as "lt";
  latexdef "lt" as "\mathrm{lt}";
htmldef "lub" as
    "<IMG SRC='_lub.gif' WIDTH=20 HEIGHT=19 ALT=' lub' TITLE='lub'>";
  althtmldef "lub" as "lub";
  latexdef "lub" as "\mathrm{lub}";
htmldef "glb" as
    "<IMG SRC='_glb.gif' WIDTH=20 HEIGHT=19 ALT=' glb' TITLE='glb'>";
  althtmldef "glb" as "glb";
  latexdef "glb" as "\mathrm{glb}";
htmldef "join" as
    "<IMG SRC='_join.gif' WIDTH=25 HEIGHT=19 ALT=' join' TITLE='join'>";
  althtmldef "join" as "join";
  latexdef "join" as "\operatorname{join}";
htmldef "meet" as
    "<IMG SRC='_meet.gif' WIDTH=32 HEIGHT=19 ALT=' meet' TITLE='meet'>";
  althtmldef "meet" as "meet";
  latexdef "meet" as "\operatorname{meet}";
htmldef "Toset" as "Toset";
  althtmldef "Toset" as "Toset";
  latexdef "Toset" as "\mathrm{Toset}";
htmldef "1." as
    "<IMG SRC='_1dot.gif' WIDTH=10 HEIGHT=19 ALT=' 1.' TITLE='1.'>";
  althtmldef "1." as "1.";
  latexdef "1." as "1.";
htmldef "0." as
    "<IMG SRC='_0dot.gif' WIDTH=11 HEIGHT=19 ALT=' 0.' TITLE='0.'>";
  althtmldef "0." as "0.";
  latexdef "0." as "0.";
htmldef "Lat" as
    "<IMG SRC='_lat.gif' WIDTH=23 HEIGHT=19 ALT=' Lat' TITLE='Lat'>";
  althtmldef "Lat" as "Lat";
  latexdef "Lat" as "\mathrm{Lat}";
htmldef "CLat" as
    "<IMG SRC='_clat.gif' WIDTH=33 HEIGHT=19 ALT=' CLat' TITLE='CLat'>";
  althtmldef "CLat" as "CLat";
  latexdef "CLat" as "\mathrm{CLat}";
htmldef "ODual" as "ODual";
  althtmldef "ODual" as "ODual";
  latexdef "ODual" as "\mathrm{ODual}";
htmldef "toInc" as "toInc";
  althtmldef "toInc" as "toInc";
  latexdef "toInc" as "\mathrm{toInc}";
htmldef "DLat" as "DLat";
  althtmldef "DLat" as "DLat";
  latexdef "DLat" as "\mathrm{DLat}";
htmldef "PosetRel" as
    "<IMG SRC='_posetrel.gif' WIDTH=56 HEIGHT=19 " +
    "ALT=' PosetRel' TITLE='PosetRel'>";
  althtmldef "PosetRel" as "PosetRel";
  latexdef "PosetRel" as "\mathrm{PosetRel}";
htmldef "TosetRel" as " <IMG SRC='_tosetrel.gif' WIDTH=55 HEIGHT=19 " +
    "ALT=' TosetRel' TITLE='TosetRel'> ";
  althtmldef "TosetRel" as " TosetRel ";
  latexdef "TosetRel" as "\mathrm{TosetRel}";
htmldef "DirRel" as
    "<IMG SRC='_dirrel.gif' WIDTH=41 HEIGHT=19 ALT=' DirRel' TITLE='DirRel'>";
  althtmldef "DirRel" as "DirRel";
  latexdef "DirRel" as "\mathrm{DirRel}";
htmldef "tail" as
    "<IMG SRC='_tail.gif' WIDTH=22 HEIGHT=19 ALT=' tail' TITLE='tail'>";
  althtmldef "tail" as "tail";
  latexdef "tail" as "\operatorname{tail}";
htmldef "Chain" as " Chain ";
  althtmldef "Chain" as " Chain ";
  latexdef "Chain" as "\mathrm{Chain}";
htmldef "Mgm" as 'Mgm';
  althtmldef "Mgm" as 'Mgm';
  latexdef "Mgm" as "\mathrm{Mgm}";
htmldef "Smgrp" as 'Smgrp';
  althtmldef "Smgrp" as 'Smgrp';
  latexdef "Smgrp" as "\mathrm{Smgrp}";
htmldef "Mnd" as
    "<IMG SRC='_mnd.gif' WIDTH=28 HEIGHT=19 ALT=' Mnd' TITLE='Mnd'>";
  althtmldef "Mnd" as "Mnd";
  latexdef "Mnd" as "\mathrm{Mnd}";
htmldef "Grp" as
    "<IMG SRC='_grp.gif' WIDTH=25 HEIGHT=19 ALT=' Grp' TITLE='Grp'>";
  althtmldef "Grp" as "Grp";
  latexdef "Grp" as "\mathrm{Grp}";
htmldef "invg" as "<IMG SRC='_inv.gif' WIDTH=19 HEIGHT=19 ALT=' inv' " +
    "TITLE='inv'><IMG SRC='subg.gif' WIDTH=7 HEIGHT=19 ALT='g' TITLE='g'>";
  althtmldef "invg" as "inv<SUB>g</SUB>";
  latexdef "invg" as "\operatorname{\mathrm{inv}_\mathrm{g}}";
htmldef "+f" as "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>" +
    "<IMG SRC='subf.gif' WIDTH=6 HEIGHT=19 ALT='f' TITLE='f'>";
  althtmldef "+f" as '+<SUB>&#x1D453;</SUB>';
  latexdef "+f" as "+_f";
htmldef "-g" as
    "<IMG SRC='_minusg.gif' WIDTH=17 HEIGHT=19 ALT=' -g' TITLE='-g'>";
  althtmldef "-g" as "-<SUB>g</SUB>";
  latexdef "-g" as "-_\mathrm{g}";
htmldef ".g" as ".<SUB>g</SUB>";
  althtmldef ".g" as ".<SUB>g</SUB>";
  latexdef ".g" as "\cdot_\mathrm{g}";
htmldef "MndHom" as " MndHom ";
  althtmldef "MndHom" as " MndHom ";
  latexdef "MndHom" as " \mathrm{MndHom} ";
htmldef "SubMnd" as "SubMnd";
  althtmldef "SubMnd" as "SubMnd";
  latexdef "SubMnd" as "\mathrm{SubMnd}";
htmldef "Word" as "Word ";
  althtmldef "Word" as "Word ";
  latexdef "Word" as "\mathrm{Word}";
htmldef "lastS" as 'lastS';
  althtmldef "lastS" as 'lastS';
  latexdef "lastS" as "\mathrm{lastS}";
htmldef "++" as " ++ ";
  althtmldef "++" as " ++ ";
  latexdef "++" as "\mathbin{\operatorname{++}}";
htmldef '<"' as
    "<IMG SRC='langle.gif' WIDTH=4 HEIGHT=19 ALT=' &lt;' TITLE='&lt;'>" +
    "<IMG SRC='backquote.gif' WIDTH=7 HEIGHT=19 ALT='" + '"' +
      "' TITLE='" + '"' + "'>";
  althtmldef '<"' as '&lang;&ldquo;'; /* &#9001;&#8220; */
  latexdef '<"' as "\langle``";
htmldef '">' as
    "<IMG SRC='quote.gif' WIDTH=7 HEIGHT=19 ALT=' " + '"' +
      "' TITLE='" + '"' + "'>" +
    "<IMG SRC='rangle.gif' WIDTH=4 HEIGHT=19 ALT='&gt;' TITLE='&gt;'>";
  althtmldef '">' as '&rdquo;&rang;'; /* &#8221;&#9002; */
  latexdef '">' as "''\rangle";
htmldef "substr" as " substr ";
  althtmldef "substr" as " substr ";
  latexdef "substr" as "\mathrm{substr}";
htmldef "splice" as " splice ";
  althtmldef "splice" as " splice ";
  latexdef "splice" as "\mathrm{splice}";
htmldef "reverse" as "reverse";
  althtmldef "reverse" as "reverse";
  latexdef "reverse" as "\mathrm{reverse}";
htmldef "repeatS" as ' repeatS ';
  althtmldef "repeatS" as ' repeatS ';
  latexdef "repeatS" as "\mathrm{repeatS}";
htmldef "cyclShift" as ' cyclShift ';
  althtmldef "cyclShift" as ' cyclShift ';
  latexdef "cyclShift" as "\mathrm{cyclShift}";
htmldef "freeMnd" as "freeMnd";
  althtmldef "freeMnd" as "freeMnd";
  latexdef "freeMnd" as "\mathrm{freeMnd}";
htmldef "varFMnd" as "var<SUB><I>FMnd</I></SUB>";
  althtmldef "varFMnd" as "var<SUB><I>FMnd</I></SUB>";
  latexdef "varFMnd" as "\mathrm{var}_{FMnd}";
htmldef "~QG" as " ~<sub><i>QG</i></sub> ";
  althtmldef "~QG" as " ~<sub><i>QG</i></sub> ";
  latexdef "~QG" as " \sim_{QG} ";
htmldef "SubGrp" as "SubGrp";
  althtmldef "SubGrp" as "SubGrp";
  latexdef "SubGrp" as "\mathrm{SubGrp}";
htmldef "NrmSGrp" as "NrmSGrp";
  althtmldef "NrmSGrp" as "NrmSGrp";
  latexdef "NrmSGrp" as "\mathrm{NrmSGrp}";
htmldef "GrpHom" as
   " <IMG SRC='_grphom.gif' WIDTH=54 HEIGHT=19 ALT=' GrpHom' TITLE='GrpHom'> ";
  althtmldef "GrpHom" as " GrpHom ";
  latexdef "GrpHom" as "\mathrm{GrpHom}";
htmldef "GrpIso" as " GrpIso ";
  althtmldef "GrpIso" as " GrpIso ";
  latexdef "GrpIso" as "\mathrm{GrpIso}";
htmldef "~=g" as " <IMG SRC='simeq.gif' WIDTH=26 HEIGHT=19 " +
    "ALT=' ~=g' TITLE='~=g'><SUB>&#x1D454;</SUB> ";
  althtmldef "~=g" as " &#8771;<SUB>&#x1D454;</SUB> ";
  latexdef "~=g" as "\simeq_{g}";
htmldef "GrpAct" as
   " <IMG SRC='_grpact.gif' WIDTH=48 HEIGHT=19 ALT=' GrpAct' TITLE='GrpAct'> ";
  althtmldef "GrpAct" as " GrpAct ";
  latexdef "GrpAct" as "\mathrm{GrpAct}";
htmldef "od" as "<IMG SRC='_od.gif' WIDTH=15 HEIGHT=19 ALT=' od' TITLE='od'>";
  althtmldef "od" as "od";
  latexdef "od" as "\mathrm{od}";
htmldef "gEx" as "gEx";
  althtmldef "gEx" as "gEx";
  latexdef "gEx" as "\mathrm{gEx}";
htmldef "pGrp" as " pGrp ";
  althtmldef "pGrp" as " pGrp ";
  latexdef "pGrp" as "\mathrm{pGrp}";
htmldef "pSyl" as " pSyl ";
  althtmldef "pSyl" as " pSyl ";
  latexdef "pSyl" as "\mathrm{pSyl}";
htmldef "~FG" as " ~<sub><i>FG</i></sub> ";
  althtmldef "~FG" as " ~<sub><i>FG</i></sub> ";
  latexdef "~FG" as " \sim_{FG} ";
htmldef "freeGrp" as "freeGrp";
  althtmldef "freeGrp" as "freeGrp";
  latexdef "freeGrp" as "\mathrm{freeGrp}";
htmldef "varFGrp" as "var<SUB><I>FGrp</I></SUB>";
  althtmldef "varFGrp" as "var<SUB><I>FGrp</I></SUB>";
  latexdef "varFGrp" as "\mathrm{var}_{FGrp}";
htmldef "CMnd" as "CMnd";
  althtmldef "CMnd" as "CMnd";
  latexdef "CMnd" as "\mathrm{CMnd}";
htmldef "CycGrp" as "CycGrp";
  althtmldef "CycGrp" as "CycGrp";
  latexdef "CycGrp" as "\mathrm{CycGrp}";
htmldef "DProd" as " DProd ";
  althtmldef "DProd" as " DProd ";
  latexdef "DProd" as "\mathrm{DProd}";
htmldef "dProj" as "dProj";
  althtmldef "dProj" as "dProj";
  latexdef "dProj" as "\mathrm{dProj}";
htmldef "Abel" as
    "<IMG SRC='_abel.gif' WIDTH=28 HEIGHT=19 ALT=' Abel' TITLE='Abel'>";
  althtmldef "Abel" as "Abel";
  latexdef "Abel" as "\mathrm{Abel}";
htmldef "oppG" as "opp<sub><i>g</i></sub>";
  althtmldef "oppG" as "opp<sub><i>g</i></sub>";
  latexdef "oppG" as "\mathrm{opp}_g";
htmldef "SymGrp" as
    "<IMG SRC='_symgrp.gif' WIDTH=53 HEIGHT=19 ALT=' SymGrp' TITLE='SymGrp'>";
  althtmldef "SymGrp" as "SymGrp";
  latexdef "SymGrp" as "\mathrm{SymGrp}";
htmldef "pmTrsp" as "pmTrsp";
  althtmldef "pmTrsp" as "pmTrsp";
  latexdef "pmTrsp" as "\operatorname{pmTrsp}";
htmldef "pmSgn" as "pmSgn";
  althtmldef "pmSgn" as "pmSgn";
  latexdef "pmSgn" as "\operatorname{pmSgn}";
htmldef "pmEven" as "pmEven";
  althtmldef "pmEven" as "pmEven";
  latexdef "pmEven" as "\operatorname{pmEven}";
htmldef "mulGrp" as "mulGrp";
  althtmldef "mulGrp" as "mulGrp";
  latexdef "mulGrp" as "\mathrm{mulGrp}";
htmldef "SRing" as "SRing";
  althtmldef "SRing" as "SRing";
  latexdef "SRing" as "\mathrm{SRing}";
htmldef "Rng" as 'Rng';
 althtmldef "Rng" as 'Rng';
 latexdef "Rng" as "\mathrm{Rng}";
htmldef "Ring" as
    "<IMG SRC='_ring.gif' WIDTH=30 HEIGHT=19 ALT=' Ring' TITLE='Ring'>";
  althtmldef "Ring" as "Ring";
  latexdef "Ring" as "\mathrm{Ring}";
htmldef "CRing" as
    "<IMG SRC='_cring.gif' WIDTH=40 HEIGHT=19 ALT=' CRing' TITLE='CRing'>";
  althtmldef "CRing" as "CRing";
  latexdef "CRing" as "\mathrm{CRing}";
htmldef "LRing" as "LRing";
  althtmldef "LRing" as "LRing";
  latexdef "LRing" as "\mathrm{LRing}";
htmldef "1r" as "<IMG SRC='_1r.gif' WIDTH=13 HEIGHT=19 ALT=' 1r' TITLE='1r'>";
  althtmldef "1r" as "1<SUB>r</SUB>";
  latexdef "1r" as "1_\mathrm{r}";
htmldef "oppR" as "opp<sub><i>r</i></sub>";
  althtmldef "oppR" as "opp<sub><i>r</i></sub>";
  latexdef "oppR" as "\mathrm{opp}_r";
htmldef "||r" as "<IMG SRC='parallel.gif' WIDTH=5 HEIGHT=19 ALT=' ||' " +
    "TITLE='||'><sub><i>r</i></sub>";
  althtmldef "||r" as "&#8741;<sub>r</sub>";
  latexdef "||r" as "\mathrel{\parallel_\mathrm{r}}";
htmldef "Unit" as "Unit";
  althtmldef "Unit" as "Unit";
  latexdef "Unit" as "\mathrm{Unit}";
htmldef "Irred" as "Irred";
  althtmldef "Irred" as "Irred";
  latexdef "Irred" as "\mathrm{Irred}";
htmldef "invr" as
    "<IMG SRC='_invr.gif' WIDTH=23 HEIGHT=19 ALT=' invr' TITLE='invr'>";
  althtmldef "invr" as "inv<SUB>r</SUB>";
  latexdef "invr" as "\mathrm{inv}_r";
htmldef "/r" as "/<SUB>r</SUB>";
  althtmldef "/r" as "/<SUB>r</SUB>";
  latexdef "/r" as "/_r";
htmldef "RPrime" as "RPrime";
  althtmldef "RPrime" as "RPrime";
  latexdef "RPrime" as "\textsc{RPrime}";
htmldef "RngHom" as ' RngHom ';
 althtmldef "RngHom" as ' RngHom ';
 latexdef "RngHom" as "\mathrm{RngHom}";
htmldef "RngIso" as ' RngIso ';
 althtmldef "RngIso" as ' RngIso ';
 latexdef "RngIso" as "\mathrm{RngIso}";
htmldef "RingHom" as " RingHom ";
  althtmldef "RingHom" as " RingHom ";
  latexdef "RingHom" as " \mathrm{RingHom} ";
htmldef "RingIso" as " RingIso ";
  althtmldef "RingIso" as " RingIso ";
  latexdef "RingIso" as " \mathrm{RingIso} ";
htmldef "~=r" as
    " <IMG SRC='_simeqr.gif' WIDTH=18 HEIGHT=19 ALT=' ~=r' TITLE='~=r'> ";
  althtmldef "~=r" as " &#8771;<SUB>&#x1D45F;</SUB> ";
  latexdef "~=r" as "\simeq_r";
htmldef "NzRing" as "NzRing";
  althtmldef "NzRing" as "NzRing";
  latexdef "NzRing" as "\mathrm{NzRing}";
htmldef "SubRng" as "SubRng";
  althtmldef "SubRng" as "SubRng";
  latexdef "SubRng" as "\mathrm{SubRng}";
htmldef "SubRing" as "SubRing";
  althtmldef "SubRing" as "SubRing";
  latexdef "SubRing" as "\mathrm{SubRing}";
htmldef "RingSpan" as "RingSpan";
  althtmldef "RingSpan" as "RingSpan";
  latexdef "RingSpan" as "\mathrm{RingSpan}";
htmldef "RngCat" as 'RngCat';
 althtmldef "RngCat" as 'RngCat';
 latexdef "RngCat" as "\mathrm{RngCat}";
htmldef "RingCat" as 'RingCat';
 althtmldef "RingCat" as 'RingCat';
 latexdef "RingCat" as "\mathrm{RingCat}";
htmldef "DivRing" as
  "<IMG SRC='_divring.gif' WIDTH=52 HEIGHT=19 ALT=' DivRing' TITLE='DivRing'>";
  althtmldef "DivRing" as "DivRing";
  latexdef "DivRing" as "\mathrm{DivRing}";
htmldef "Field" as "Field";
  althtmldef "Field" as "Field";
  latexdef "Field" as "\mathrm{Field}";
htmldef "AbsVal" as "AbsVal";
  althtmldef "AbsVal" as "AbsVal";
  latexdef "AbsVal" as "\operatorname{AbsVal}";
htmldef "*Ring" as "<IMG SRC='_astring.gif' " +
    "WIDTH=41 HEIGHT=19 ALT=' *Ring' TITLE='*Ring'>";
  althtmldef "*Ring" as "*-Ring";
  latexdef "*Ring" as "\ast\mathrm{-Ring}";
htmldef "*rf" as "<IMG SRC='ast.gif' WIDTH=7 HEIGHT=19 ALT=' *' TITLE='*'>" +
    "<IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 ALT='r' TITLE='r'>" +
    "<IMG SRC='subf.gif' WIDTH=6 HEIGHT=19 ALT='f' TITLE='f'>";
  althtmldef "*rf" as "*<SUB><I>rf</I></SUB>";
  latexdef "*rf" as "\ast_{rf}";
htmldef "LMod" as
    "<IMG SRC='_lmod.gif' WIDTH=36 HEIGHT=19 ALT=' LMod' TITLE='LMod'>";
  althtmldef "LMod" as "LMod";
  latexdef "LMod" as "\mathrm{LMod}";
htmldef ".sf" as
    "<IMG SRC='_cds.gif' WIDTH=9 HEIGHT=19 ALT=' .s' TITLE='.s'>" +
    "<IMG SRC='subf.gif' WIDTH=6 HEIGHT=19 ALT='f' TITLE='f'>";
  althtmldef ".sf" as ' <B>&middot;</B><SUB><I>sf</I></SUB> ';
  latexdef ".sf" as '\cdot_{sf}';
htmldef "LSubSp" as
    "<IMG SRC='_lsubsp.gif' WIDTH=49 HEIGHT=19 ALT=' LSubSp' TITLE='LSubSp'>";
  althtmldef "LSubSp" as "LSubSp";
  latexdef "LSubSp" as "\mathrm{LSubSp}";
htmldef "LSpan" as
    "<IMG SRC='_lspan.gif' WIDTH=41 HEIGHT=19 ALT=' LSpan' TITLE='LSpan'>";
  althtmldef "LSpan" as "LSpan";
  latexdef "LSpan" as "\mathrm{LSpan}";
htmldef "LMHom" as " LMHom ";
  althtmldef "LMHom" as " LMHom ";
  latexdef "LMHom" as "\mathrm{LMHom}";
htmldef "LMIso" as " LMIso ";
  althtmldef "LMIso" as " LMIso ";
  latexdef "LMIso" as "\mathrm{LMIso}";
htmldef "~=m" as " <IMG SRC='simeq.gif' WIDTH=26 HEIGHT=19 " +
    "ALT=' ~=ph' TITLE='~=ph'><SUB>&#x1D45A;</SUB> ";
  althtmldef "~=m" as " &#8771;<SUB>&#x1D45A;</SUB> ";
  latexdef "~=m" as "\simeq_{m}";
htmldef "LBasis" as "LBasis";
  althtmldef "LBasis" as "LBasis";
  latexdef "LBasis" as "\mathrm{LBasis}";
htmldef "LSSum" as
    "<IMG SRC='_lssum.gif' WIDTH=45 HEIGHT=19 ALT=' LSSum' TITLE='LSSum'>";
  althtmldef "LSSum" as "LSSum";
  latexdef "LSSum" as "\mathrm{LSSum}";
htmldef "proj1" as
    "<IMG SRC='_proj.gif' WIDTH=24 HEIGHT=19 ALT=' proj' TITLE='proj'>" +
    "<IMG SRC='sub1.gif' WIDTH=4 HEIGHT=19 ALT='1' TITLE='1'>";
  althtmldef "proj1" as 'proj<SUB>1</SUB>';
  latexdef "proj1" as '\mathrm{proj}_1';
htmldef "LVec" as
    "<IMG SRC='_lvec.gif' WIDTH=33 HEIGHT=19 ALT=' LVec' TITLE='LVec'>";
  althtmldef "LVec" as "LVec";
  latexdef "LVec" as "\mathrm{LVec}";
htmldef "subringAlg" as "subringAlg ";
  althtmldef "subringAlg" as "subringAlg ";
  latexdef "subringAlg" as "\mathrm{subringAlg}";
htmldef "ringLMod" as "ringLMod";
  althtmldef "ringLMod" as "ringLMod";
  latexdef "ringLMod" as "\mathrm{ringLMod}";
htmldef "RSpan" as "RSpan";
  althtmldef "RSpan" as "RSpan";
  latexdef "RSpan" as "\mathrm{RSpan}";
htmldef "LIdeal" as "LIdeal";
  althtmldef "LIdeal" as "LIdeal";
  latexdef "LIdeal" as "\mathrm{LIdeal}";
htmldef "2Ideal" as "2Ideal";
  althtmldef "2Ideal" as "2Ideal";
  latexdef "2Ideal" as "\mathrm{2Ideal}";
htmldef "LPIdeal" as "LPIdeal";
  althtmldef "LPIdeal" as "LPIdeal";
  latexdef "LPIdeal" as "\mathrm{LPIdeal}";
/*
htmldef "Top1c" as "Top1c";
  althtmldef "Top1c" as "Top1c";
  latexdef "Top1c" as "\mathrm{Top1c}";
htmldef "Top2c" as "Top2c";
  althtmldef "Top2c" as "Top2c";
  latexdef "Top2c" as "\mathrm{Top2c}";
*/
htmldef "LPIR" as "LPIR";
  althtmldef "LPIR" as "LPIR";
  latexdef "LPIR" as "\mathrm{LPIR}";
htmldef "RLReg" as "RLReg";
  althtmldef "RLReg" as "RLReg";
  latexdef "RLReg" as "\mathrm{RLReg}";
htmldef "Domn" as "Domn";
  althtmldef "Domn" as "Domn";
  latexdef "Domn" as "\mathrm{Domn}";
htmldef "IDomn" as "IDomn";
  althtmldef "IDomn" as "IDomn";
  latexdef "IDomn" as "\mathrm{IDomn}";
htmldef "PID" as "PID";
  althtmldef "PID" as "PID";
  latexdef "PID" as "\mathrm{PID}";
/*
htmldef "UFD" as "UFD";
  althtmldef "UFD" as "UFD";
  latexdef "UFD" as "\textsc{UFD}";
*/
htmldef "*Met" as
    "<IMG SRC='infty.gif' WIDTH=17 HEIGHT=19 ALT=' *' TITLE='*'>" +
    "<IMG SRC='_met.gif' WIDTH=25 HEIGHT=19 ALT='Met' TITLE='Met'>";
  althtmldef "*Met" as "&infin;Met";
  latexdef "*Met" as "\infty\mathrm{Met}";
htmldef "Met" as
    "<IMG SRC='_met.gif' WIDTH=25 HEIGHT=19 ALT=' Met' TITLE='Met'>";
  althtmldef "Met" as "Met";
  latexdef "Met" as "\mathrm{Met}";
htmldef "ball" as
    "<IMG SRC='_ball.gif' WIDTH=24 HEIGHT=19 ALT=' ball' TITLE='ball'>";
  althtmldef "ball" as "ball";
  latexdef "ball" as "\mathrm{ball}";
htmldef "MetOpen" as
  "<IMG SRC='_metopen.gif' WIDTH=59 HEIGHT=19 ALT=' MetOpen' TITLE='MetOpen'>";
  althtmldef "MetOpen" as "MetOpen";
  latexdef "MetOpen" as "\mathrm{MetOpen}";
htmldef "CCfld" as "&#8450;<SUB>fld</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  althtmldef "CCfld" as "&#8450;<SUB>fld</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "CCfld" as "\mathrm{CCfld}";
htmldef "ZZring" as "&#8484;<SUB>ring</SUB>";
  althtmldef "ZZring" as "&#8484;<SUB>ring</SUB>";
  latexdef "ZZring" as "\mathrm{ZZring}";
htmldef "RR^" as "&#8477;^";
  althtmldef "RR^" as "&#8477;^";
  latexdef "RR^" as "\mathbb{R}\hat{\;}";
htmldef "EEhil" as "&#x1D53C;<SUB>hil</SUB>";
  althtmldef "EEhil" as "&#x1D53C;<SUB>hil</SUB>";
  latexdef "EEhil" as "\mathrm{EEhil}";
htmldef "ZRHom" as
    "<IMG SRC='bbz.gif' WIDTH=13 HEIGHT=19 ALT=' Z' TITLE='Z'>RHom";
  althtmldef "ZRHom" as "&#8484;RHom";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "ZRHom" as "\mathrm{ZRHom}";
htmldef "ZMod" as
    "<IMG SRC='bbz.gif' WIDTH=13 HEIGHT=19 ALT=' Z' TITLE='Z'>Mod";
  althtmldef "ZMod" as "&#8484;Mod";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "ZMod" as "\mathrm{ZMod}";
htmldef "chr" as "chr";
  althtmldef "chr" as "chr";
  latexdef "chr" as "\mathrm{chr}";
htmldef "Z/nZ" as "&#8484;/<i>n</i>&#8484;";
    /* 2-Jan-2016 reverted sans-serif */
  althtmldef "Z/nZ" as "&#8484;/<i>n</i>&#8484;";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "Z/nZ" as "\mathrm{Z/nZ}";
htmldef "RRfld" as "RRfld";
  althtmldef "RRfld" as "&#8477;<SUB>fld</SUB>";
  latexdef "RRfld" as "\mathbb{R}_\mathrm{fld}";
htmldef "PreHil" as
    "<IMG SRC='_prehil.gif' WIDTH=40 HEIGHT=19 ALT=' PreHil' TITLE='PreHil'>";
  althtmldef "PreHil" as "PreHil";
  latexdef "PreHil" as "\mathrm{PreHil}";
htmldef ".if" as
    "<IMG SRC='_cdi.gif' WIDTH=7 HEIGHT=19 ALT=' .i' TITLE='.i'>" +
    "<IMG SRC='subf.gif' WIDTH=6 HEIGHT=19 ALT='f' TITLE='f'>";
  althtmldef ".if" as '<B>&middot;</B><SUB><I>if</I></SUB>';
  latexdef ".if" as '\cdot_{if}';
htmldef "ocv" as
    "<IMG SRC='_ocv.gif' WIDTH=22 HEIGHT=19 ALT=' ocv' TITLE='ocv'>";
  althtmldef "ocv" as "ocv";
  latexdef "ocv" as "\mathrm{ocv}";
htmldef "ClSubSp" as
    "<IMG SRC='_csubsp.gif' WIDTH=50 HEIGHT=19 ALT='ClSubSp' TITLE='ClSubSp'>";
  althtmldef "ClSubSp" as "ClSubSp";
  latexdef "ClSubSp" as "\mathrm{ClSubSp}";
htmldef "toHL" as "toHL";
  althtmldef "toHL" as "toHL";
  latexdef "toHL" as "\mathrm{toHL}";
htmldef "proj" as
    "<IMG SRC='_proj.gif' WIDTH=24 HEIGHT=19 ALT=' proj' TITLE='proj'>";
  althtmldef "proj" as 'proj';
  latexdef "proj" as '\operatorname{proj}';
htmldef "Hil" as
    "<IMG SRC='_hil.gif' WIDTH=18 HEIGHT=19 ALT=' Hil' TITLE='Hil'>";
  althtmldef "Hil" as "Hil";
  latexdef "Hil" as "\mathrm{Hil}";
htmldef "OBasis" as "OBasis";
  althtmldef "OBasis" as "OBasis";
  latexdef "OBasis" as "\mathrm{OBasis}";
htmldef "Moore" as "Moore";
  althtmldef "Moore" as "Moore";
  latexdef "Moore" as "\mathrm{Moore}";
htmldef "mrCls" as "mrCls";
  althtmldef "mrCls" as "mrCls";
  latexdef "mrCls" as "\mathrm{mrCls}";
htmldef "mrInd" as "mrInd";
  althtmldef "mrInd" as "mrInd";
  latexdef "mrInd" as "\mathrm{mrInd}";
htmldef "ACS" as "ACS";
  althtmldef "ACS" as "ACS";
  latexdef "ACS" as "\mathrm{ACS}";

/* Basic linear algebra */
htmldef "(+)m" as " <IMG SRC='oplus.gif' WIDTH=13 HEIGHT=19 " +
    "ALT=' (+)' TITLE='(+)'><SUB>m</SUB> ";
  althtmldef "(+)m" as " &#x2295;<SUB>m</SUB> ";
  latexdef "(+)m" as "\oplus_{m}";
htmldef "freeLMod" as " freeLMod ";
  althtmldef "freeLMod" as " freeLMod ";
  latexdef "freeLMod" as "\mathrm{freeLMod}";
htmldef "unitVec" as " unitVec ";
  althtmldef "unitVec" as " unitVec ";
  latexdef "unitVec" as "\mathrm{unitVec}";
htmldef "AssAlg" as "AssAlg";
  althtmldef "AssAlg" as "AssAlg";
  latexdef "AssAlg" as "\mathrm{AssAlg}";
htmldef "AlgSpan" as "AlgSpan";
  althtmldef "AlgSpan" as "AlgSpan";
  latexdef "AlgSpan" as "\mathrm{AlgSpan}";
htmldef "algSc" as "algSc";
  althtmldef "algSc" as "algSc";
  latexdef "algSc" as "\mathrm{algSc}";
htmldef "mPwSer" as " mPwSer ";
  althtmldef "mPwSer" as " mPwSer ";
  latexdef "mPwSer" as "\mathrm{mPwSer}";
htmldef "mVar" as " mVar ";
  althtmldef "mVar" as " mVar ";
  latexdef "mVar" as "\mathrm{mVar}";
htmldef "mPoly" as " mPoly ";
  althtmldef "mPoly" as " mPoly ";
  latexdef "mPoly" as "\mathrm{mPoly}";
htmldef "evalSub" as " evalSub ";
  althtmldef "evalSub" as " evalSub ";
  latexdef "evalSub" as "\mathbin{\operatorname{evalSub}}";
htmldef "eval" as " eval ";
  althtmldef "eval" as " eval ";
  latexdef "eval" as "\mathbin{\operatorname{eval}}";
htmldef "mHomP" as " mHomP ";
  althtmldef "mHomP" as " mHomP ";
  latexdef "mHomP" as "\mathrm{mHomP}";
htmldef "mPSDer" as " mPSDer ";
  althtmldef "mPSDer" as " mPSDer ";
  latexdef "mPSDer" as "\mathrm{mPSDer}";
htmldef "<bag" as " <IMG SRC='lt.gif' WIDTH=11 HEIGHT=19 ALT=' &lt;' " +
    "TITLE='&lt;'><sub>bag</sub> ";
  althtmldef "<bag" as " &lt;<sub>bag</sub> ";
  latexdef "<bag" as "<_\mathrm{bag}";
htmldef "ordPwSer" as " ordPwSer ";
  althtmldef "ordPwSer" as " ordPwSer ";
  latexdef "ordPwSer" as "\mathrm{ordPwSer}";
htmldef "selectVars" as " selectVars ";
  althtmldef "selectVars" as " selectVars ";
  latexdef "selectVars" as "\mathrm{selectVars}";
htmldef "mDeg" as " mDeg ";
  althtmldef "mDeg" as " mDeg ";
  latexdef "mDeg" as "\mathrm{mDeg}";
htmldef "AlgInd" as " AlgInd ";
  althtmldef "AlgInd" as " AlgInd ";
  latexdef "AlgInd" as " \mathrm{AlgInd} ";
htmldef "PwSer1" as "PwSer<sub>1</sub>";
  althtmldef "PwSer1" as "PwSer<sub>1</sub>";
  latexdef "PwSer1" as "\mathrm{PwSer}_1";
htmldef "var1" as "var<sub>1</sub>";
  althtmldef "var1" as "var<sub>1</sub>";
  latexdef "var1" as "\mathrm{var}_1";
htmldef "Poly1" as "Poly<sub>1</sub>";
  althtmldef "Poly1" as "Poly<sub>1</sub>";
  latexdef "Poly1" as "\mathrm{Poly}_1";
htmldef "evalSub1" as " evalSub<sub>1</sub> ";
  althtmldef "evalSub1" as " evalSub<sub>1</sub> ";
  latexdef "evalSub1" as " \mathrm{evalSub}_1 ";
htmldef "eval1" as "eval<sub>1</sub>";
  althtmldef "eval1" as "eval<sub>1</sub>";
  latexdef "eval1" as "\mathrm{eval}_1";
htmldef "deg1" as "deg<sub>1</sub>";
  althtmldef "deg1" as "deg<sub>1</sub>";
  latexdef "deg1" as "\mathrm{deg}_1";
htmldef "coe1" as "coe<sub>1</sub>";
  althtmldef "coe1" as "coe<sub>1</sub>";
  latexdef "coe1" as "\mathrm{coe}_1";
htmldef "toPoly1" as "toPoly<sub>1</sub>";
  althtmldef "toPoly1" as "toPoly<sub>1</sub>";
  latexdef "toPoly1" as "\mathrm{toPoly}_1";
htmldef "maMul" as " maMul ";
  althtmldef "maMul" as " maMul ";
  latexdef "maMul" as " \mathrm{maMul} ";
htmldef "Mat" as " Mat ";
  althtmldef "Mat" as " Mat ";
  latexdef "Mat" as " \mathrm{Mat} ";
htmldef "DMat" as ' DMat ';
  althtmldef "DMat" as ' DMat ';
  latexdef "DMat" as "\mathrm{DMat}";
htmldef "ScMat" as ' ScMat ';
  althtmldef "ScMat" as ' ScMat ';
  latexdef "ScMat" as "\mathrm{ScMat}";
htmldef "maVecMul" as " maVecMul ";
  althtmldef "maVecMul" as " maVecMul ";
  latexdef "maVecMul" as " \mathrm{maVecMul} ";
htmldef "matRRep" as " matRRep ";
  althtmldef "matRRep" as " matRRep ";
  latexdef "matRRep" as " \mathrm{matRRep} ";
htmldef "matRepV" as " matRepV ";
  althtmldef "matRepV" as " matRepV ";
  latexdef "matRepV" as " \mathrm{matRepV} ";
htmldef "maDet" as " maDet ";
  althtmldef "maDet" as " maDet ";
  latexdef "maDet" as " \mathrm{maDet} ";
htmldef "maAdju" as " maAdju ";
  althtmldef "maAdju" as " maAdju ";
  latexdef "maAdju" as " \mathrm{maAdju} ";
htmldef "subMat" as " subMat ";
  althtmldef "subMat" as " subMat ";
  latexdef "subMat" as " \mathrm{subMat} ";
htmldef "minMatR1" as " minMatR1 ";
  althtmldef "minMatR1" as " minMatR1 ";
  latexdef "minMatR1" as " \mathrm{minMatR1} ";
htmldef "ConstPolyMat" as ' ConstPolyMat ';
  althtmldef "ConstPolyMat" as ' ConstPolyMat ';
  latexdef "ConstPolyMat" as "\mathrm{ConstPolyMat}";
htmldef "matToPolyMat" as ' matToPolyMat ';
  althtmldef "matToPolyMat" as ' matToPolyMat ';
  latexdef "matToPolyMat" as "\mathrm{matToPolyMat}";
htmldef "cPolyMatToMat" as ' cPolyMatToMat ';
  althtmldef "cPolyMatToMat" as ' cPolyMatToMat ';
  latexdef "cPolyMatToMat" as "\mathrm{cPolyMatToMat}";
htmldef "decompPMat" as ' decompPMat ';
  althtmldef "decompPMat" as ' decompPMat ';
  latexdef "decompPMat" as "\mathrm{decompPMat}";
htmldef "pMatToMatPoly" as ' pMatToMatPoly ';
  althtmldef "pMatToMatPoly" as ' pMatToMatPoly ';
  latexdef "pMatToMatPoly" as "\mathrm{pMatToMatPoly}";
htmldef "CharPlyMat" as ' CharPlyMat ';
  althtmldef "CharPlyMat" as ' CharPlyMat ';
  latexdef "CharPlyMat" as "\mathrm{CharPlyMat}";

/* Topology */
htmldef "Top" as
    "<IMG SRC='_top.gif' WIDTH=23 HEIGHT=19 ALT=' Top' TITLE='Top'>";
  althtmldef "Top" as "Top";
  latexdef "Top" as "\mathrm{Top}";
htmldef "TopOn" as "TopOn";
  althtmldef "TopOn" as "TopOn";
  latexdef "TopOn" as "\mathrm{TopOn}";
htmldef "TopSp" as
    "<IMG SRC='_topsp.gif' WIDTH=41 HEIGHT=19 ALT=' TopSp' TITLE='TopSp'>";
  althtmldef "TopSp" as "TopSp";
  latexdef "TopSp" as "\mathrm{TopSp}";
htmldef "TopBases" as
    "<IMG SRC='_topbases.gif' WIDTH=59 HEIGHT=19 " +
    "ALT=' TopBases' TITLE='TopBases'>";
  althtmldef "TopBases" as "TopBases";
  latexdef "TopBases" as "\mathrm{TopBases}";
htmldef "int" as
    "<IMG SRC='_int.gif' WIDTH=18 HEIGHT=19 ALT=' int' TITLE='int'>";
  althtmldef "int" as "int";
  latexdef "int" as "\mathrm{int}";
htmldef "cls" as
    "<IMG SRC='_cls.gif' WIDTH=17 HEIGHT=19 ALT=' cls' TITLE='cls'>";
  althtmldef "cls" as "cls";
  latexdef "cls" as "\mathrm{cls}";
htmldef "Clsd" as
    "<IMG SRC='_clsd.gif' WIDTH=28 HEIGHT=19 ALT=' Clsd' TITLE='Clsd'>";
  althtmldef "Clsd" as "Clsd";
  latexdef "Clsd" as "\mathrm{Clsd}";
htmldef "nei" as
    "<IMG SRC='_nei.gif' WIDTH=19 HEIGHT=19 ALT=' nei' TITLE='nei'>";
  althtmldef "nei" as "nei";
  latexdef "nei" as "\mathrm{nei}";
htmldef "limPt" as
    "<IMG SRC='_limpt.gif' WIDTH=35 HEIGHT=19 ALT=' limPt' TITLE='limPt'>";
  althtmldef "limPt" as "limPt";
  latexdef "limPt" as "\mathrm{limPt}";
htmldef "Perf" as "Perf";
  althtmldef "Perf" as "Perf";
  latexdef "Perf" as "\mathrm{Perf}";
htmldef "Cn" as
    " <IMG SRC='_cnf.gif' WIDTH=18 HEIGHT=19 ALT=' Cn' TITLE='Cn'> ";
  althtmldef "Cn" as " Cn ";
  latexdef "Cn" as "\mathrm{Cn}";
htmldef "CnP" as
    " <IMG SRC='_cnp.gif' WIDTH=27 HEIGHT=19 ALT=' CnP' TITLE='CnP'> ";
  althtmldef "CnP" as " CnP ";
  latexdef "CnP" as "\mathrm{CnP}";
htmldef "~~>t" as "<IMG SRC='rightsquigarrow.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' ~~&gt;' TITLE='~~&gt;'>" +
    "<IMG SRC='subt.gif' WIDTH=5 HEIGHT=19 ALT=' t' TITLE='t'>";
  althtmldef "~~>t" as
    "&#8669;<SUB>&#x1D461;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~~>t" as "\rightsquigarrow_t";
htmldef "Kol2" as
    "<IMG SRC='_kol2.gif' WIDTH=27 HEIGHT=19 ALT=' Kol2' TITLE='Kol2'>";
  althtmldef "Kol2" as "Kol2";
  latexdef "Kol2" as "\mathrm{Kol2}";
htmldef "Fre" as
    "<IMG SRC='_fre.gif' WIDTH=22 HEIGHT=19 ALT=' Fre' TITLE='Fre'>";
  althtmldef "Fre" as "Fre";
  latexdef "Fre" as "\mathrm{Fre}";
htmldef "Haus" as
    "<IMG SRC='_haus.gif' WIDTH=32 HEIGHT=19 ALT=' Haus' TITLE='Haus'>";
  althtmldef "Haus" as "Haus";
  latexdef "Haus" as "\mathrm{Haus}";
htmldef "Reg" as
    "<IMG SRC='_reg.gif' WIDTH=25 HEIGHT=19 ALT=' Reg' TITLE='Reg'>";
  althtmldef "Reg" as "Reg";
  latexdef "Reg" as "\mathrm{Reg}";
htmldef "Nrm" as
    "<IMG SRC='_nrm.gif' WIDTH=28 HEIGHT=19 ALT=' Nrm' TITLE='Nrm'>";
  althtmldef "Nrm" as "Nrm";
  latexdef "Nrm" as "\mathrm{Nrm}";
htmldef "CNrm" as "CNrm";
  althtmldef "CNrm" as "CNrm";
  latexdef "CNrm" as "\mathrm{CNrm}";
htmldef "PNrm" as "PNrm";
  althtmldef "PNrm" as "PNrm";
  latexdef "PNrm" as "\mathrm{PNrm}";
htmldef "Comp" as
    "<IMG SRC='_comp.gif' WIDTH=37 HEIGHT=19 ALT=' Comp' TITLE='Comp'>";
  althtmldef "Comp" as "Comp";
  latexdef "Comp" as "\mathrm{Comp}";
htmldef "Conn" as "Conn";
  althtmldef "Conn" as "Conn";
  latexdef "Conn" as "\mathrm{Conn}";
htmldef "1stc" as "<IMG SRC='_1stc.gif' WIDTH=25 HEIGHT=19 ALT=' 1stc'" +
    " TITLE='1stc'>";
  althtmldef "1stc" as "1<SUP>st</SUP>&#x3C9;";  /* upright lowercase omega */
  latexdef "1stc" as "1^\text{st}\omega";
htmldef "2ndc" as "<IMG SRC='_2ndc.gif' WIDTH=31 HEIGHT=19 ALT=' 2ndc'" +
    " TITLE='2ndc'>";
  althtmldef "2ndc" as "2<SUP>nd</SUP>&#x3c9;";  /* upright lowercase omega */
  latexdef "2ndc" as "2^\text{nd}\omega";
htmldef "Locally" as "Locally ";
  althtmldef "Locally" as "Locally ";
  latexdef "Locally" as "\mathrm{Locally}";
htmldef "N-Locally" as "&#x1D45B;Locally ";
  althtmldef "N-Locally" as "&#x1D45B;-Locally ";
  latexdef "N-Locally" as "n\text{-Locally }";
htmldef "kGen" as "&#x1D458;Gen";
  althtmldef "kGen" as "&#x1D458;Gen";
  latexdef "kGen" as "k\mathrm{Gen}";
htmldef "tX" as
    " <IMG SRC='_timest.gif' WIDTH=14 HEIGHT=19 ALT=' tX' TITLE='tX'> ";
  althtmldef "tX" as " &times;<SUB>t</SUB> ";
  latexdef "tX" as "\times_t";
htmldef "^ko" as
    " <IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' ^' TITLE='^'>" +
    "<IMG SRC='subk.gif' WIDTH=7 HEIGHT=19 ALT='k' TITLE='k'>" +
    "<IMG SRC='subo.gif' WIDTH=6 HEIGHT=19 ALT='o' TITLE='o'> ";
  althtmldef "^ko" as " &uarr;<SUB>ko</SUB> ";
  latexdef "^ko" as "\mathbin{\uparrow_text{ko}}";
htmldef "KQ" as "KQ";
  althtmldef "KQ" as "KQ";
  latexdef "KQ" as "\mathrm{KQ}";
htmldef "Homeo" as
    "<IMG SRC='_homeo.gif' WIDTH=43 HEIGHT=19 ALT=' Homeo' TITLE='Homeo'>";
  althtmldef "Homeo" as "Homeo";
  latexdef "Homeo" as "\mathrm{Homeo}";
htmldef "~=" as
    " <IMG SRC='simeq.gif' WIDTH=13 HEIGHT=19 ALT=' ~=' TITLE='~='> ";
  althtmldef "~=" as " &#8771; ";
  latexdef "~=" as "\simeq";
htmldef "fBas" as
    "<IMG SRC='_fbas.gif' WIDTH=29 HEIGHT=19 ALT=' fBas' TITLE='fBas'>";
  althtmldef "fBas" as "fBas";
  latexdef "fBas" as "\mathrm{fBas}";
htmldef "filGen" as
    "<IMG SRC='_filgen.gif' WIDTH=40 HEIGHT=19 ALT=' filGen' TITLE='filGen'>";
  althtmldef "filGen" as "filGen";
  latexdef "filGen" as "\mathrm{filGen}";
htmldef "Fil" as
    "<IMG SRC='_fil.gif' WIDTH=17 HEIGHT=19 ALT=' Fil' TITLE='Fil'>";
  althtmldef "Fil" as "Fil";
  latexdef "Fil" as "\mathrm{Fil}";
htmldef "UFil" as
    "<IMG SRC='_ufil.gif' WIDTH=27 HEIGHT=19 ALT=' UFil' TITLE='UFil'>";
  althtmldef "UFil" as "UFil";
  latexdef "UFil" as "\mathrm{UFil}";
htmldef "UFL" as "UFL";
  althtmldef "UFL" as "UFL";
  latexdef "UFL" as "\mathrm{UFL}";
htmldef "FilMap" as
   " <IMG SRC='_filmap.gif' WIDTH=45 HEIGHT=19 ALT=' FilMap' TITLE='FilMap'> ";
  althtmldef "FilMap" as " FilMap ";
  latexdef "FilMap" as "\mathbin{\mathrm{FilMap}}";
htmldef "fLimf" as
    " <IMG SRC='_flimf.gif' WIDTH=37 HEIGHT=19 ALT=' fLimf' TITLE='fLimf'> ";
  althtmldef "fLimf" as " fLimf ";
  latexdef "fLimf" as "\mathbin{\mathrm{fLimf}}";
htmldef "fLim" as
    " <IMG SRC='_flim.gif' WIDTH=31 HEIGHT=19 ALT=' fLim' TITLE='fLim'> ";
  althtmldef "fLim" as " fLim ";
  latexdef "fLim" as "\mathbin{\mathrm{fLim}}";
htmldef "fClus" as
    " <IMG SRC='_fclus.gif' WIDTH=34 HEIGHT=19 ALT=' fClus' TITLE='fClus'> ";
  althtmldef "fClus" as " fClus ";
  latexdef "fClus" as "\mathbin{\mathrm{fClus}}";
htmldef "fClusf" as
   " <IMG SRC='_fclusf.gif' WIDTH=40 HEIGHT=19 ALT=' fClusf' TITLE='fClusf'> ";
  althtmldef "fClusf" as " fClusf ";
  latexdef "fClusf" as "\mathbin{\mathrm{fClusf}}";
htmldef "TopMnd" as "TopMnd";
  althtmldef "TopMnd" as "TopMnd";
  latexdef "TopMnd" as "\mathrm{TopMnd}";
htmldef "TopGrp" as
    "<IMG SRC='_topgrp.gif' WIDTH=48 HEIGHT=19 ALT=' TopGrp' TITLE='TopGrp'>";
  althtmldef "TopGrp" as "TopGrp";
  latexdef "TopGrp" as "\mathrm{TopGrp}";
htmldef "tsums" as " tsums ";
  althtmldef "tsums" as " tsums ";
  latexdef "tsums" as "\mathrm{tsums}";
htmldef "TopRing" as
    "<IMG SRC='_topring.gif' WIDTH=53 HEIGHT=19 " +
    "ALT=' TopRing' TITLE='TopRing'>";
  althtmldef "TopRing" as "TopRing";
  latexdef "TopRing" as "\mathrm{TopRing}";
htmldef "TopDRing" as "TopDRing";
  althtmldef "TopDRing" as "TopDRing";
  latexdef "TopDRing" as "\mathrm{TopDRing}";
htmldef "TopMod" as "TopMod";
  althtmldef "TopMod" as "TopMod";
  latexdef "TopMod" as "\mathrm{TopMod}";
htmldef "TopVec" as
    "<IMG SRC='_topvec.gif' WIDTH=43 HEIGHT=19 ALT=' TopVec' TITLE='TopVec'>";
  althtmldef "TopVec" as "TopVec";
  latexdef "TopVec" as "\mathrm{TopVec}";
htmldef "*MetSp" as
    "<IMG SRC='infty.gif' WIDTH=17 HEIGHT=19 ALT=' *' TITLE='*'>" +
    "<IMG SRC='_metsp.gif' WIDTH=41 HEIGHT=19 ALT='MetSp' TITLE='MetSp'>";
  althtmldef "*MetSp" as "&infin;MetSp";
  latexdef "*MetSp" as "\infty\mathrm{MetSp}";
htmldef "MetSp" as
    "<IMG SRC='_metsp.gif' WIDTH=41 HEIGHT=19 ALT=' MetSp' TITLE='MetSp'>";
  althtmldef "MetSp" as "MetSp";
  latexdef "MetSp" as "\mathrm{MetSp}";
htmldef "toMetSp" as "toMetSp";
  althtmldef "toMetSp" as "toMetSp";
  latexdef "toMetSp" as "\mathrm{toMetSp}";
htmldef "norm" as "<IMG SRC='_norm.gif' WIDTH=32 HEIGHT=19 ALT=' norm' " +
    "TITLE='norm'>";
  althtmldef "norm" as 'norm';
  latexdef "norm" as '\operatorname{norm}';
htmldef "NrmGrp" as "NrmGrp";
  althtmldef "NrmGrp" as "NrmGrp";
  latexdef "NrmGrp" as "\mathrm{NrmGrp}";
htmldef "toNrmGrp" as " toNrmGrp ";
  althtmldef "toNrmGrp" as " toNrmGrp ";
  latexdef "toNrmGrp" as "\mathrm{toNrmGrp}";
htmldef "NrmRing" as "NrmRing";
  althtmldef "NrmRing" as "NrmRing";
  latexdef "NrmRing" as "\mathrm{NrmRing}";
htmldef "NrmMod" as "NrmMod";
  althtmldef "NrmMod" as "NrmMod";
  latexdef "NrmMod" as "\mathrm{NrmMod}";
htmldef "NrmVec" as "NrmVec";
  althtmldef "NrmVec" as "NrmVec";
  latexdef "NrmVec" as "\mathrm{NrmVec}";
htmldef "normOp" as
    "<IMG SRC='_normop.gif' WIDTH=52 HEIGHT=19 ALT=' normOp' TITLE='normOp'>";
  althtmldef "normOp" as " normOp ";
  latexdef "normOp" as "\mathbin{\operatorname{normOp}}";
htmldef "NGHom" as " NGHom ";
  althtmldef "NGHom" as " NGHom ";
  latexdef "NGHom" as "\mathrm{NGHom}";
htmldef "NMHom" as " NMHom ";
  althtmldef "NMHom" as " NMHom ";
  latexdef "NMHom" as "\mathrm{NMHom}";
htmldef "II" as "<IMG SRC='bbi.gif' WIDTH=7 HEIGHT=19 ALT=' II' TITLE='II'>";
  althtmldef "II" as "II";
  latexdef "II" as "\mathrm{II}";
htmldef "-cn->" as "<IMG SRC='_cnmap.gif' WIDTH=23 HEIGHT=19 " +
    "ALT=' -cn-&gt;' TITLE='-cn-&gt;'>";
  althtmldef "-cn->" as '&ndash;<FONT SIZE=-1 FACE=sans-serif>cn</FONT>&rarr;';
  latexdef "-cn->" as "\overset{\mathrm{cn}}{\longrightarrow}";
htmldef "Htpy" as " Htpy ";
  althtmldef "Htpy" as " Htpy ";
  latexdef "Htpy" as "\mathrm{Htpy}";
htmldef "PHtpy" as
    "<IMG SRC='_phtpy.gif' WIDTH=41 HEIGHT=19 ALT=' PHtpy' TITLE='PHtpy'>";
  althtmldef "PHtpy" as "PHtpy";
  latexdef "PHtpy" as "\mathrm{PHtpy}";
htmldef "~=ph" as
    " <IMG SRC='_simeqph.gif' WIDTH=26 HEIGHT=19 ALT=' ~=ph' TITLE='~=ph'> ";
  althtmldef "~=ph" as " &#8771;<SUB><I>ph</I></SUB>";
  latexdef "~=ph" as "\simeq_{ph}";
/*
htmldef "pi1b" as
    "<IMG SRC='pi.gif' WIDTH=10 HEIGHT=19 ALT=' pi' TITLE='pi'>" +
    "<IMG SRC='sub1.gif' WIDTH=4 HEIGHT=19 ALT='1' TITLE='1'>" +
    "<IMG SRC='subb.gif' WIDTH=6 HEIGHT=19 ALT='b' TITLE='b'>";
  althtmldef "pi1b" as "<I>&pi;<SUB>1b</SUB></I>";
  latexdef "pi1b" as "\pi_{1b}";
*/
htmldef "*p" as
    "<IMG SRC='_astp.gif' WIDTH=14 HEIGHT=19 ALT=' *p' TITLE='*p'>";
  althtmldef "*p" as "*<SUB>&#x1D45D;</SUB>";
  latexdef "*p" as "*_p";
htmldef "Om1" as
    " <IMG SRC='comega.gif' WIDTH=11 HEIGHT=19 ALT=' Om' TITLE='Om'>" +
    "<IMG SRC='sub1.gif' WIDTH=4 HEIGHT=19 ALT='1' TITLE='1'> ";
  althtmldef "Om1" as " &Omega;<SUB>1</SUB> ";
  latexdef "Om1" as "\Omega_1";
htmldef "OmN" as
    " <IMG SRC='comega.gif' WIDTH=11 HEIGHT=19 ALT=' Om' TITLE='Om'>" +
    "<IMG SRC='subn.gif' WIDTH=6 HEIGHT=19 ALT='N' TITLE='N'> ";
  althtmldef "OmN" as " &Omega;<SUB>&#x1D45B;</SUB> ";
  latexdef "OmN" as "\Omega_n";
htmldef "pi1" as
    " <IMG SRC='pi.gif' WIDTH=10 HEIGHT=19 ALT=' pi' TITLE='pi'>" +
    "<IMG SRC='sub1.gif' WIDTH=4 HEIGHT=19 ALT='1' TITLE='1'> ";
  althtmldef "pi1" as " &pi;<SUB>1</SUB> ";
  latexdef "pi1" as "\mathrm{\pi_1}";
htmldef "piN" as
    " <IMG SRC='pi.gif' WIDTH=10 HEIGHT=19 ALT=' pi' TITLE='pi'>" +
    "<IMG SRC='subn.gif' WIDTH=6 HEIGHT=19 ALT='N' TITLE='N'> ";
  althtmldef "piN" as " &pi;<SUB>n</SUB> ";
  latexdef "piN" as "\mathrm{\pi_n}";
/*
htmldef "~~>m" as "<IMG SRC='_squigm.gif' WIDTH=25 HEIGHT=19 " +
    "ALT=' ~~&gt;m' TITLE='~~&gt;m'>";
  althtmldef "~~>m" as '<FONT FACE=sans-serif>&#8669;<SUB>m</SUB></FONT>';
  latexdef "~~>m" as "\rightsquigarrow_\mathrm{m}";
*/
htmldef "CMod" as "CMod";
  althtmldef "CMod" as "&#8450;Mod";
  latexdef "CMod" as "{\mathbb{C}\mathrm{Mod}}";
htmldef "CVec" as "CVec";
  althtmldef "CVec" as "&#8450;Vec";
  latexdef "CVec" as "{\mathbb{C}\mathrm{Vec}}";
htmldef "CPreHil" as
  "<IMG SRC='_cprehil.gif' WIDTH=50 HEIGHT=19 ALT=' CPreHil' TITLE='CPreHil'>";
  althtmldef "CPreHil" as "&#8450;PreHil";
  latexdef "CPreHil" as "{\mathbb{C}\mathrm{PreHil}}";
htmldef "toCPreHil" as "toCPreHil";
  althtmldef "toCPreHil" as "to&#8450;PreHil";
  latexdef "toCPreHil" as "{\mathrm{to}\mathbb{C}\mathrm{PreHil}}";
htmldef "CauFil" as "CauFil";
  althtmldef "CauFil" as "CauFil";
  latexdef "CauFil" as "\mathrm{CauFil}";
htmldef "Cau" as
    "<IMG SRC='_cau.gif' WIDTH=26 HEIGHT=19 ALT=' Cau' TITLE='Cau'>";
  althtmldef "Cau" as "Cau";
  latexdef "Cau" as "\mathrm{Cau}";
htmldef "CMet" as
    "<IMG SRC='_cmet.gif' WIDTH=35 HEIGHT=19 ALT=' CMet' TITLE='CMet'>";
  althtmldef "CMet" as "CMet";
  latexdef "CMet" as "\mathrm{CMet}";
htmldef "CMetSp" as "CMetSp";
  althtmldef "CMetSp" as "CMetSp";
  latexdef "CMetSp" as "\mathrm{CMetSp}";
htmldef "Ban" as "Ban";
  althtmldef "Ban" as "Ban";
  latexdef "Ban" as "\mathrm{Ban}";
htmldef "CHil" as
    "<IMG SRC='_chil.gif' WIDTH=28 HEIGHT=19 ALT=' CHil' TITLE='CHil'>";
  althtmldef "CHil" as "&#8450;Hil";
  latexdef "CHil" as "{\mathbb{C}\mathrm{Hil}}";
htmldef "vol*" as
    "<IMG SRC='_vol.gif' WIDTH=19 HEIGHT=19 ALT=' vol' TITLE='vol'>" +
    "<IMG SRC='supast.gif' WIDTH=6 HEIGHT=19 ALT='*' TITLE='*'>";
  althtmldef "vol*" as "vol*";
  latexdef "vol*" as "\operatorname{vol}^*";
htmldef "vol" as
    "<IMG SRC='_vol.gif' WIDTH=19 HEIGHT=19 ALT=' vol' TITLE='vol'>";
  althtmldef "vol" as "vol";
  latexdef "vol" as "\mathrm{vol}";
htmldef "MblFn" as "MblFn";
  althtmldef "MblFn" as "MblFn";
  latexdef "MblFn" as "\mathrm{MblFn}";
htmldef "L^1" as
    "<IMG SRC='cl.gif' WIDTH=10 HEIGHT=19 ALT=' L' TITLE='L'>" +
    "<IMG SRC='sup1.gif' WIDTH=4 HEIGHT=19 ALT='^1' TITLE='^1'>";
  althtmldef "L^1" as "&#x1D43F;<SUP>1</SUP>";
  latexdef "L^1" as "L^1";
htmldef "S.1" as
    "<IMG SRC='_int1.gif' WIDTH=11 HEIGHT=19 ALT=' S.1' TITLE='S.1'>";
  althtmldef "S.1" as "&int;<SUB>1</SUB>";
  latexdef "S.1" as "\int_2";
htmldef "S.2" as
    "<IMG SRC='_int2.gif' WIDTH=13 HEIGHT=19 ALT=' S.2' TITLE='S.2'>";
  althtmldef "S.2" as "&int;<SUB>2</SUB>";
  latexdef "S.2" as "\int_2";
htmldef "S." as "<IMG SRC='int.gif' WIDTH=10 HEIGHT=19 ALT=' S.' TITLE='S.'>";
  althtmldef "S." as "&int;";
  latexdef "S." as "\int";
htmldef "S_" as "<IMG SRC='int.gif' WIDTH=10 HEIGHT=19 ALT=' S_' TITLE='S_'>_";
  althtmldef "S_" as "&#x2A1C;";
  latexdef "S_" as "\int";
htmldef "_d" as " <IMG SRC='rmd.gif' WIDTH=8 HEIGHT=19 ALT=' _d' TITLE='_d'>";
  althtmldef "_d" as " d";
  latexdef "_d" as "\,\mathrm{d}";
htmldef "0p" as "<IMG SRC='0.gif' WIDTH=8 HEIGHT=19 ALT=' 0' TITLE='0'>" +
    "<IMG SRC='subp.gif' WIDTH=7 HEIGHT=19 ALT='p' TITLE='p'>";
  althtmldef "0p" as "0<SUB>&#x1D45D;</SUB>";
  latexdef "0p" as "0_p";
htmldef "_D" as
    " <IMG SRC='rmcd.gif' WIDTH=10 HEIGHT=19 ALT=' _D' TITLE='_D'> ";
  althtmldef "_D" as " D ";
  latexdef "_D" as "\mathbin{\mathrm{D}}";
htmldef "limCC" as
    " lim<IMG SRC='bbc.gif' WIDTH=12 HEIGHT=19 ALT=' CC' TITLE='CC'> ";
  althtmldef "limCC" as " lim<sub>&#8450;</sub> ";
  latexdef "limCC" as "\mathbin{\lim_\mathbb{C}}";
htmldef "Dn" as
    " <IMG SRC='rmcd.gif' WIDTH=10 HEIGHT=19 ALT=' D' TITLE='D'>" +
    "<IMG SRC='supn.gif' WIDTH=6 HEIGHT=19 ALT='n' TITLE='n'>";
  althtmldef "Dn" as " D<SUP>&#x1D45B;</SUP> ";
  latexdef "Dn" as "\mathbin{\mathrm{D}^n}";
htmldef "C^n" as "<IMG SRC='cc.gif' WIDTH=12 HEIGHT=19 ALT=' C' TITLE='C'>" +
    "<IMG SRC='supn.gif' WIDTH=6 HEIGHT=19 ALT='^n' TITLE='^n'>";
  althtmldef "C^n" as "&#x1D4D1;C<SUP>&#x1D45B;</SUP>";
  latexdef "C^n" as "\operatorname{\mathcal{C}^n}";
htmldef "Monic1p" as "Monic<sub>1p</sub>";
  althtmldef "Monic1p" as "Monic<sub>1p</sub>";
  latexdef "Monic1p" as "\mathrm{Monic}_{1p}";
htmldef "Unic1p" as "Unic<sub>1p</sub>";
  althtmldef "Unic1p" as "Unic<sub>1p</sub>";
  latexdef "Unic1p" as "\mathrm{Unic}_{1p}";
htmldef "quot1p" as "quot<sub>1p</sub>";
  althtmldef "quot1p" as "quot<sub>1p</sub>";
  latexdef "quot1p" as "\mathrm{quot}_{1p}";
htmldef "rem1p" as "rem<sub>1p</sub>";
  althtmldef "rem1p" as "rem<sub>1p</sub>";
  latexdef "rem1p" as "\mathrm{rem}_{1p}";
htmldef "idlGen1p" as "idlGen<sub>1p</sub>";
  althtmldef "idlGen1p" as "idlGen<sub>1p</sub>";
  latexdef "idlGen1p" as "\mathrm{idlGen}_{1p}";
htmldef "Poly" as "Poly";
  althtmldef "Poly" as "Poly";
  latexdef "Poly" as "\mathrm{Poly}";
htmldef "Xp" as "<IMG SRC='cx.gif' WIDTH=13 HEIGHT=19 ALT=' X' TITLE='X'>" +
    "<IMG SRC='subp.gif' WIDTH=7 HEIGHT=19 ALT='p' TITLE='p'>";
  althtmldef "Xp" as "<I>X<SUB>p</SUB></I>";
  latexdef "Xp" as "X_p";
htmldef "coeff" as "coeff";
  althtmldef "coeff" as "coeff";
  latexdef "coeff" as "\mathrm{coeff}";
htmldef "deg" as "deg";
  althtmldef "deg" as "deg";
  latexdef "deg" as "\operatorname{deg}";
htmldef "quot" as " quot ";
  althtmldef "quot" as " quot ";
  latexdef "quot" as "\mathrm{quot}";
htmldef "AA" as "<IMG SRC='bba.gif' WIDTH=13 HEIGHT=19 ALT=' AA' TITLE='AA'>";
  althtmldef "AA" as '&#120120;';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "AA" as "\mathbb{A}";
htmldef "Tayl" as " Tayl ";
  althtmldef "Tayl" as " Tayl ";
  latexdef "Tayl" as "\mathrm{Tayl}";
htmldef "Ana" as "Ana";
  althtmldef "Ana" as "Ana";
  latexdef "Ana" as "\mathrm{Ana}";
htmldef "~~>u" as "<IMG SRC='rightsquigarrow.gif' WIDTH=15 HEIGHT=19 " +
    "ALT=' ~~&gt;' TITLE='~~&gt;'>" +
    "<IMG SRC='subu.gif' WIDTH=6 HEIGHT=19 ALT=' u' TITLE='u'>";
  althtmldef "~~>u" as
    "&#8669;<SUB>&#x1D462;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~~>u" as "\rightsquigarrow_u";
htmldef "log" as
    "<IMG SRC='_log.gif' WIDTH=20 HEIGHT=19 ALT=' log' TITLE='log'>";
  althtmldef "log" as "log";
  latexdef "log" as "\log";
htmldef "logb" as " log<sub>b</sub> ";
  althtmldef "logb" as " log<sub>b</sub> ";
  latexdef "logb" as "\mathrm{log}_b";
htmldef "^c" as
    " <IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' ^' TITLE='^'>" +
    "<IMG SRC='subc.gif' WIDTH=6 HEIGHT=19 ALT='c' TITLE='c'> ";
  althtmldef "^c" as "&uarr;<SUB>&#x1D450;</SUB>";
  latexdef "^c" as "\uparrow_c";
htmldef "arcsin" as "arcsin";
  althtmldef "arcsin" as "arcsin";
  latexdef "arcsin" as "\arcsin";
htmldef "arccos" as "arccos";
  althtmldef "arccos" as "arccos";
  latexdef "arccos" as "\arccos";
htmldef "arctan" as "arctan";
  althtmldef "arctan" as "arctan";
  latexdef "arctan" as "\arctan";
htmldef "area" as "area";
  althtmldef "area" as "area";
  latexdef "area" as "\mathrm{area}";
htmldef "gamma" as
    "<IMG SRC='gamma.gif' WIDTH=11 HEIGHT=19 ALT=' gamma' TITLE='gamma'>";
  althtmldef "gamma" as "&gamma;";
  latexdef "gamma" as "\gamma";
htmldef "theta" as
    "<IMG SRC='theta.gif' WIDTH=8 HEIGHT=19 ALT=' theta' TITLE='theta'>";
  althtmldef "theta" as "&theta;";
  latexdef "theta" as "\theta";
htmldef "Lam" as "&Lambda;";
  althtmldef "Lam" as "&Lambda;";
  latexdef "Lam" as "\Lambda";
htmldef "psi" as "&psi;";
  althtmldef "psi" as "&psi;";
  latexdef "psi" as "\psi";
htmldef "ppi" as "<U>&pi;</U>";
  althtmldef "ppi" as "<U>&pi;</U>";
  latexdef "ppi" as "\pi";
htmldef "mmu" as
    "<IMG SRC='mu.gif' WIDTH=10 HEIGHT=19 ALT=' mmu' TITLE='mmu'>";
  althtmldef "mmu" as "&mu;";
  latexdef "mmu" as "\mu";
htmldef "sigma" as
    " <IMG SRC='sigma.gif' WIDTH=10 HEIGHT=19 ALT=' sigma' TITLE='sigma'> ";
  althtmldef "sigma" as " &sigma; ";
  latexdef "sigma" as "\sigma";
htmldef "DChr" as "DChr";
  althtmldef "DChr" as "DChr";
  latexdef "DChr" as "\mathrm{DChr}";
htmldef "/L" as
    " <IMG SRC='solidus.gif' WIDTH=6 HEIGHT=19 ALT=' /' TITLE='/'>" +
    "<IMG SRC='subcl.gif' WIDTH=8 HEIGHT=19 ALT='L' TITLE='L'>";
  althtmldef "/L" as " /<sub><i>L</i></sub> ";
  latexdef "/L" as " /_L ";

/* Graph theory */
htmldef ".ef" as '.ef';
  althtmldef ".ef" as ".ef";
  latexdef ".ef" as "\mathrm{ef}";
htmldef "Vtx" as 'Vtx';
  althtmldef "Vtx" as 'Vtx';
  latexdef "Vtx" as "\mathrm{Vtx}";
htmldef "iEdg" as 'iEdg';
  althtmldef "iEdg" as 'iEdg';
  latexdef "iEdg" as "\mathrm{iEdg}";
htmldef "UHGraph" as 'UHGraph';
  althtmldef "UHGraph" as 'UHGraph';
  latexdef "UHGraph" as "\mathrm{UHGraph}";
htmldef "USHGraph" as 'USHGraph';
  althtmldef "USHGraph" as 'USHGraph';
  latexdef "USHGraph" as "\mathrm{USHGraph}";
htmldef "UPGraph" as 'UPGraph';
  althtmldef "UPGraph" as 'UPGraph';
  latexdef "UPGraph" as "\mathrm{UPGraph}";
htmldef "UMGraph" as 'UMGraph';
  althtmldef "UMGraph" as 'UMGraph';
  latexdef "UMGraph" as "\mathrm{UMGraph}";
htmldef "Edg" as 'Edg';
  althtmldef "Edg" as 'Edg';
  latexdef "Edg" as "\mathrm{Edg}";
htmldef "USPGraph" as 'USPGraph';
  althtmldef "USPGraph" as 'USPGraph';
  latexdef "USPGraph" as "\mathrm{USPGraph}";
htmldef "USGraph" as 'USGraph';
  althtmldef "USGraph" as 'USGraph';
  latexdef "USGraph" as "\mathrm{USGraph}";
htmldef "SubGraph" as ' SubGraph ';
  althtmldef "SubGraph" as ' SubGraph ';
  latexdef "SubGraph" as "\mathrm{SubGraph}";
htmldef "FinUSGraph" as 'FinUSGraph';
  althtmldef "FinUSGraph" as 'FinUSGraph';
  latexdef "FinUSGraph" as "\mathrm{FinUSGraph}";
htmldef "NeighbVtx" as ' NeighbVtx ';
  althtmldef "NeighbVtx" as ' NeighbVtx ';
  latexdef "NeighbVtx" as "\mathrm{NeighbVtx}";
htmldef "ComplGraph" as 'ComplGraph';
  althtmldef "ComplGraph" as 'ComplGraph';
  latexdef "ComplGraph" as "\mathrm{ComplGraph}";
htmldef "ComplUSGraph" as 'ComplUSGraph';
  althtmldef "ComplUSGraph" as 'ComplUSGraph';
  latexdef "ComplUSGraph" as "\mathrm{ComplUSGraph}";
htmldef "UnivVtx" as 'UnivVtx';
  althtmldef "UnivVtx" as 'UnivVtx';
  latexdef "UnivVtx" as "\mathrm{UnivVtx}";
htmldef "VtxDeg" as 'VtxDeg';
  althtmldef "VtxDeg" as 'VtxDeg';
  latexdef "VtxDeg" as "\mathrm{VtxDeg}";
htmldef "RegGraph" as ' RegGraph ';
  althtmldef "RegGraph" as ' RegGraph ';
  latexdef "RegGraph" as "\mathrm{RegGraph}";
htmldef "RegUSGraph" as ' RegUSGraph ';
  althtmldef "RegUSGraph" as ' RegUSGraph ';
  latexdef "RegUSGraph" as "\mathrm{RegUSGraph}";
htmldef "EdgWalks" as ' EdgWalks ';
  althtmldef "EdgWalks" as ' EdgWalks ';
  latexdef "EdgWalks" as "\mathrm{EdgWalks}";
htmldef "Walks" as "Walks";
  althtmldef "Walks" as "Walks";
  latexdef "Walks" as "\mathrm{Walks}";
htmldef "WalksOn" as "WalksOn";
  althtmldef "WalksOn" as "WalksOn";
  latexdef "WalksOn" as "\mathrm{WalksOn}";
htmldef "Trails" as "Trails";
  althtmldef "Trails" as "Trails";
  latexdef "Trails" as "\mathrm{Trails}";
htmldef "TrailsOn" as "TrailsOn";
  althtmldef "TrailsOn" as "TrailsOn";
  latexdef "TrailsOn" as "\mathrm{TrailsOn}";
htmldef "Paths" as "Paths";
  althtmldef "Paths" as "Paths";
  latexdef "Paths" as "\mathrm{Paths}";
htmldef "SPaths" as "SPaths";
  althtmldef "SPaths" as "SPaths";
  latexdef "SPaths" as "\mathrm{SPaths}";
htmldef "PathsOn" as "PathsOn";
  althtmldef "PathsOn" as "PathsOn";
  latexdef "PathsOn" as "\mathrm{PathsOn}";
htmldef "SPathsOn" as "SPathsOn";
  althtmldef "SPathsOn" as "SPathsOn";
  latexdef "SPathsOn" as "\mathrm{SPathsOn}";
htmldef "ClWalks" as "ClWalks";
  althtmldef "ClWalks" as "ClWalks";
  latexdef "ClWalks" as "\mathrm{ClWalks}";
htmldef "Circuits" as "Circuits";
  althtmldef "Circuits" as "Circuits";
  latexdef "Circuits" as "\mathrm{Circuits}";
htmldef "Cycles" as "Cycles";
  althtmldef "Cycles" as "Cycles";
  latexdef "Cycles" as "\mathrm{Cycles}";
htmldef "WWalks" as 'WWalks';
  althtmldef "WWalks" as 'WWalks';
  latexdef "WWalks" as "\mathrm{WWalks}";
htmldef "WWalksN" as ' WWalksN ';
  althtmldef "WWalksN" as ' WWalksN ';
  latexdef "WWalksN" as "\mathrm{WWalksN}";
htmldef "WWalksNOn" as ' WWalksNOn ';
  althtmldef "WWalksNOn" as ' WWalksNOn ';
  latexdef "WWalksNOn" as "\mathrm{WWalksNOn}";
htmldef "WSPathsN" as ' WSPathsN ';
  althtmldef "WSPathsN" as ' WSPathsN ';
  latexdef "WSPathsN" as "\mathrm{WSPathsN}";
htmldef "WSPathsNOn" as ' WSPathsNOn ';
  althtmldef "WSPathsNOn" as ' WSPathsNOn ';
  latexdef "WSPathsNOn" as "\mathrm{WSPathsNOn}";
htmldef "ClWWalks" as 'ClWWalks';
  althtmldef "ClWWalks" as 'ClWWalks';
  latexdef "ClWWalks" as "\mathrm{ClWWalks}";
htmldef "ClWWalksN" as ' ClWWalksN ';
  althtmldef "ClWWalksN" as ' ClWWalksN ';
  latexdef "ClWWalksN" as "\mathrm{ClWWalksN}";
htmldef "ClWWalksNOn" as 'ClWWalksNOn';
  althtmldef "ClWWalksNOn" as 'ClWWalksNOn';
  latexdef "ClWWalksNOn" as "\mathrm{ClWWalksNOn}";
htmldef "ConnGraph" as "ConnGraph";
  althtmldef "ConnGraph" as "ConnGraph";
  latexdef "ConnGraph" as "\mathrm{ConnGraph}";
htmldef "EulerPaths" as "EulerPaths";
  althtmldef "EulerPaths" as "EulerPaths";
  latexdef "EulerPaths" as "\mathrm{EulerPaths}";
htmldef "FriendGraph" as ' FriendGraph ';
  althtmldef "FriendGraph" as ' FriendGraph ';
  latexdef "FriendGraph" as "\mathrm{FriendGraph}";

/* Guides and miscellanea */
htmldef "Plig" as
    "<IMG SRC='_plig.gif' WIDTH=25 HEIGHT=19 ALT=' Plig' TITLE='Plig'>";
  althtmldef "Plig" as "Plig";
  latexdef "Plig" as "\mathrm{Plig}";
htmldef "t+" as "<IMG SRC='t.gif' WIDTH=7 HEIGHT=19 ALT=' t' TITLE='t'>" +
    "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT='+' TITLE='+'>";
  althtmldef "t+" as "t+";
  latexdef "t+" as "\mathrm{t}+";
htmldef "t*" as "<IMG SRC='t.gif' WIDTH=7 HEIGHT=19 ALT=' t' TITLE='t'>" +
    "<IMG SRC='ast.gif' WIDTH=7 HEIGHT=19 ALT='*' TITLE='*'>";
  althtmldef "t*" as "t*";
  latexdef "t*" as "\mathrm{t}*";
htmldef "GrpOp" as
    "<IMG SRC='_grpop.gif' WIDTH=44 HEIGHT=19 ALT=' GrpOp' TITLE='GrpOp'>";
  althtmldef "GrpOp" as "GrpOp";
  latexdef "GrpOp" as "\mathrm{GrpOp}";
htmldef "GId" as "GId";
  althtmldef "GId" as "GId";
  latexdef "GId" as "\mathrm{GId}";
htmldef "inv" as
    "<IMG SRC='_inv.gif' WIDTH=19 HEIGHT=19 ALT=' inv' TITLE='inv'>";
  althtmldef "inv" as "inv";
  latexdef "inv" as "\mathrm{inv}";
htmldef "/g" as " <IMG SRC='_divg.gif' WIDTH=11 HEIGHT=19 ALT=' /g' " +
    "TITLE='/g'> ";
  althtmldef "/g" as " /<SUB>&#x1D454;</SUB> ";
  latexdef "/g" as "/_g";
htmldef "AbelOp" as
    "<IMG SRC='_abelop.gif' WIDTH=47 HEIGHT=19 ALT=' AbelOp' TITLE='AbelOp'>";
  althtmldef "AbelOp" as "AbelOp";
  latexdef "AbelOp" as "\mathrm{AbelOp}";
htmldef "Ass" as
    "<IMG SRC='_ass.gif' WIDTH=22 HEIGHT=19 ALT=' Ass' TITLE='Ass'>";
  althtmldef "Ass" as "Ass";
  latexdef "Ass" as "\mathrm{Ass}";
htmldef "ExId" as
    " <IMG SRC='_exid.gif' WIDTH=29 HEIGHT=19 ALT=' ExId' TITLE='ExId'> ";
  althtmldef "ExId" as " ExId ";
  latexdef "ExId" as "\mathrm{ExId}";
htmldef "Magma" as
    "<IMG SRC='_magma.gif' WIDTH=48 HEIGHT=19 ALT=' Magma' TITLE='Magma'>";
  althtmldef "Magma" as "Magma";
  latexdef "Magma" as "\mathrm{Magma}";
htmldef "SemiGrp" as
  "<IMG SRC='_semigrp.gif' WIDTH=56 HEIGHT=19 ALT=' SemiGrp' TITLE='SemiGrp'>";
  althtmldef "SemiGrp" as "SemiGrp";
  latexdef "SemiGrp" as "\mathrm{SemiGrp}";
htmldef "MndOp" as "MndOp";
  althtmldef "MndOp" as "MndOp";
  latexdef "MndOp" as "\mathrm{MndOp}";
htmldef "GrpOpHom" as " GrpOpHom ";
  althtmldef "GrpOpHom" as " GrpOpHom ";
  latexdef "GrpOpHom" as "\mathrm{GrpOpHom}";
htmldef "RingOps" as
  "<IMG SRC='_ringops.gif' WIDTH=55 HEIGHT=19 ALT=' RingOps' TITLE='RingOps'>";
  althtmldef "RingOps" as "RingOps";
  latexdef "RingOps" as "\mathrm{RingOps}";
htmldef "DivRingOps" as "<IMG SRC='_divringops.gif' WIDTH=77 HEIGHT=19" +
      " ALT=' DivRingOps' TITLE='DivRingOps'>";
  althtmldef "DivRingOps" as "DivRingOps";
  latexdef "DivRingOps" as "\mathrm{DivRingOps}";
htmldef "Com2" as
    "<IMG SRC='_com2.gif' WIDTH=35 HEIGHT=19 ALT=' Com2' TITLE='Com2'>";
  althtmldef "Com2" as "Com2";
  latexdef "Com2" as "\mathrm{Com2}";
htmldef "Fld" as
    "<IMG SRC='_fld.gif' WIDTH=21 HEIGHT=19 ALT=' Fld' TITLE='Fld'>";
  althtmldef "Fld" as "Fld";
  latexdef "Fld" as "\mathrm{Fld}";
htmldef "CVecOLD" as
    "<IMG SRC='_cvec.gif' WIDTH=34 HEIGHT=19 ALT=' CVec' TITLE='CVec'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT='OLD' TITLE='OLD'>";
  althtmldef "CVecOLD" as "CVec<SUB>OLD</SUB>";
  latexdef "CVecOLD" as "\mathrm{CVec_{OLD}}";
htmldef "NrmCVec" as
  "<IMG SRC='_nrmcvec.gif' WIDTH=62 HEIGHT=19 ALT=' NrmCVec' TITLE='NrmCVec'>";
  althtmldef "NrmCVec" as "NrmCVec";
  latexdef "NrmCVec" as "\mathrm{NrmCVec}";
htmldef "+v" as "<IMG SRC='_plv.gif' WIDTH=19 HEIGHT=19 ALT=' +v' TITLE='+v'>";
  althtmldef "+v" as ' +<SUB>&#x1D463;</SUB> ';
  latexdef "+v" as '+_v';
htmldef "BaseSet" as
  "<IMG SRC='_baseset.gif' WIDTH=51 HEIGHT=19 ALT=' BaseSet' TITLE='BaseSet'>";
  althtmldef "BaseSet" as "BaseSet";
  latexdef "BaseSet" as "\mathrm{BaseSet}";
htmldef ".sOLD" as
    "<IMG SRC='_cds.gif' WIDTH=9 HEIGHT=19 ALT=' .s' TITLE='.s'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT='OLD' TITLE='OLD'>";
  althtmldef ".sOLD" as ' <B>&middot;</B><SUB>&#x1D460;OLD</SUB> ';
  latexdef ".sOLD" as '\cdot_{s\mathrm{OLD}}';
htmldef "0vec" as
    "<IMG SRC='_0vec.gif' WIDTH=25 HEIGHT=19 ALT=' 0vec' TITLE='0vec'>";
  althtmldef "0vec" as '0<SUB>vec</SUB>';
  latexdef "0vec" as '0_\mathrm{vec}';
htmldef "-v" as "<IMG SRC='_mv.gif' WIDTH=17 HEIGHT=19 ALT=' -v' TITLE='-v'>";
  althtmldef "-v" as ' &minus;<SUB>&#x1D463;</SUB> ';
  latexdef "-v" as '-_v';
htmldef "normCV" as "<IMG SRC='_norm.gif' WIDTH=32 HEIGHT=19 ALT=' norm' " +
    "TITLE='norm'><SUB>CV</SUB>";
  althtmldef "normCV" as 'norm<SUB>CV</SUB>';
  latexdef "normCV" as '\mathrm{norm_{CV}}';
    /* 24-Apr-2007 nm These need images. */
htmldef "IndMet" as
    "<IMG SRC='_indmet.gif' WIDTH=45 HEIGHT=19 ALT=' IndMet' TITLE='IndMet'>";
  althtmldef "IndMet" as "IndMet";
  latexdef "IndMet" as "\mathrm{IndMet}";
htmldef ".iOLD" as
    "<IMG SRC='_cdi.gif' WIDTH=7 HEIGHT=19 ALT=' .i' TITLE='.i'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT='OLD' TITLE='OLD'>";
  althtmldef ".iOLD" as '<B>&middot;</B><SUB>&#x1D456;OLD</SUB>';
  latexdef ".iOLD" as '\cdot_{i\mathrm{OLD}}';
htmldef "SubSp" as
    "<IMG SRC='_subsp.gif' WIDTH=40 HEIGHT=19 ALT=' SubSp' TITLE='SubSp'>";
  althtmldef "SubSp" as "SubSp";
  latexdef "SubSp" as "\mathrm{SubSp}";
htmldef "LnOp" as
    " <IMG SRC='_lnop.gif' WIDTH=36 HEIGHT=19 ALT=' LnOp' TITLE='LnOp'> ";
  althtmldef "LnOp" as " LnOp ";
  latexdef "LnOp" as "\mathrm{LnOp}";
htmldef "normOpOLD" as
    "<IMG SRC='_normop.gif' WIDTH=52 HEIGHT=19 ALT=' normOp' TITLE='normOp'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT='OLD' TITLE='OLD'>";
  althtmldef "normOpOLD" as " normOp<SUB>OLD</SUB> ";
  latexdef "normOpOLD" as "\mathrm{normOp_{OLD}}";
htmldef "BLnOp" as
    " <IMG SRC='_blnop.gif' WIDTH=45 HEIGHT=19 ALT=' BLnOp' TITLE='BLnOp'> ";
  althtmldef "BLnOp" as " BLnOp ";
  latexdef "BLnOp" as "\mathrm{BLnOp}";
htmldef "0op" as
    " <IMG SRC='_0op.gif' WIDTH=21 HEIGHT=19 ALT=' 0op' TITLE='0op'> ";
  althtmldef "0op" as " 0<SUB>op</SUB> ";
  latexdef "0op" as "0_\mathrm{op}";
htmldef "adj" as
    "<IMG SRC='_adj.gif' WIDTH=20 HEIGHT=19 ALT=' adj' TITLE='adj'>";
  althtmldef "adj" as "adj";
  latexdef "adj" as "\mathbin{\operatorname{adj}}";
htmldef "HmOp" as
    "<IMG SRC='_hmop.gif' WIDTH=41 HEIGHT=19 ALT=' HmOp' TITLE='HmOp'>";
  althtmldef "HmOp" as "HmOp";
  latexdef "HmOp" as "\mathrm{HmOp}";
htmldef "CPreHilOLD" as
    "<IMG SRC='_cprehil.gif' WIDTH=50 HEIGHT=19 " +
    "ALT=' CPreHil' TITLE='CPreHil'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT=' OLD' TITLE='OLD'>";
  althtmldef "CPreHilOLD" as "CPreHil<SUB>OLD</SUB>";
  latexdef "CPreHilOLD" as "\mathrm{CPreHil_{OLD}}";
htmldef "CBan" as
    "<IMG SRC='_cban.gif' WIDTH=35 HEIGHT=19 ALT=' CBan' TITLE='CBan'>";
  althtmldef "CBan" as "CBan";
  latexdef "CBan" as "\mathrm{CBan}";
htmldef "CHilOLD" as
    "<IMG SRC='_chil.gif' WIDTH=28 HEIGHT=19 ALT=' CHil' TITLE='CHil'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT='OLD' TITLE='OLD'>";
  althtmldef "CHilOLD" as "CHil<SUB>OLD</SUB>";
  latexdef "CHilOLD" as "\mathrm{CHil_{OLD}}";
    /* Hilbert space */
htmldef "~H" as "<IMG SRC='scrh.gif' WIDTH=19 HEIGHT=19 ALT=' ~H' TITLE='~H'>";
  althtmldef "~H" as ' &#8459;';
    /* 8459 is script H; 8460 is fraktur H */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "~H" as '\mathscr{H}';
htmldef "+h" as
    " <IMG SRC='_pvh.gif' WIDTH=18 HEIGHT=19 ALT=' +h' TITLE='+h'> ";
  althtmldef "+h" as ' +<SUB>&#x210E;</SUB> ';
  latexdef "+h" as '+_h';
htmldef ".h" as
    " <IMG SRC='_cdh.gif' WIDTH=9 HEIGHT=19 ALT=' .h' TITLE='.h'> ";
  althtmldef ".h" as ' <B>&middot;</B><SUB>&#x210E;</SUB> ';
  latexdef ".h" as '\cdot_h';
htmldef "0h" as "<IMG SRC='_0vh.gif' WIDTH=14 HEIGHT=19 ALT=' 0h' TITLE='0h'>";
  althtmldef "0h" as '0<SUB>&#x210E;</SUB>';
  latexdef "0h" as '0_h';
htmldef "-h" as
    " <IMG SRC='_mvh.gif' WIDTH=16 HEIGHT=19 ALT=' -h' TITLE='-h'> ";
  althtmldef "-h" as ' &minus;<SUB>&#x210E;</SUB> ';
  latexdef "-h" as '-_h';
htmldef ".ih" as " <IMG SRC='_cdih.gif' WIDTH=13 HEIGHT=19 ALT=' .ih' " +
    "TITLE='.ih'> ";
  althtmldef ".ih" as ' <B>&middot;</B><SUB><I>ih</I></SUB> ';
  latexdef ".ih" as '\cdot_{ih}';
htmldef "normh" as "<IMG SRC='_normh.gif' WIDTH=38 HEIGHT=19 ALT=' normh' " +
    "TITLE='normh'>";
  althtmldef "normh" as 'norm<SUB>&#x210E;</SUB>';
  latexdef "normh" as '\mathrm{norm}_h';
htmldef "Cauchy" as "<IMG SRC='_cauchy.gif' WIDTH=47 HEIGHT=19 " +
    "ALT=' Cauchy' TITLE='Cauchy'>";
  althtmldef "Cauchy" as 'Cauchy';
  latexdef "Cauchy" as '\mathrm{Cauchy}';
htmldef "~~>v" as " <IMG SRC='_squigv.gif' WIDTH=21 HEIGHT=19 " +
    "ALT=' ~~&gt;v' TITLE='~~&gt;v'> ";
  althtmldef "~~>v" as
    ' &#8669;<SUB>&#x1D463;</SUB> ';
    /* 24-Sep-2017 reverted sans-serif */
  latexdef "~~>v" as '\rightsquigarrow_v';
htmldef "SH" as "<IMG SRC='_sh.gif' WIDTH=24 HEIGHT=19 ALT=' SH' TITLE='SH'>";
  althtmldef "SH" as
    ' <I><B>S</B></I><SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "SH" as '\mathscr{S}_\mathscr{H}';
htmldef "CH" as
    "<IMG SRC='_scrch.gif' WIDTH=22 HEIGHT=19 ALT=' CH' TITLE='CH'>";
  althtmldef "CH" as
    ' <I><B>C</B></I><SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "CH" as '\mathscr{C}_\mathscr{H}';
htmldef "_|_" as
    "<IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 ALT=' _|_' TITLE='_|_'>";
  althtmldef "_|_" as '&#8869;'; /* &bottom; */
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "_|_" as '\perp';
htmldef "+H" as
    " <IMG SRC='_plh.gif' WIDTH=24 HEIGHT=19 ALT=' +H' TITLE='+H'> ";
  althtmldef "+H" as ' +<SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "+H" as '+_\mathscr{H}';
htmldef "span" as
    "<IMG SRC='_span.gif' WIDTH=31 HEIGHT=19 ALT=' span' TITLE='span'>";
  althtmldef "span" as 'span';
  latexdef "span" as '\mathrm{span}';
htmldef "vH" as
    " <IMG SRC='_veeh.gif' WIDTH=21 HEIGHT=19 ALT=' vH' TITLE='vH'> ";
  althtmldef "vH" as ' &or;<SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "vH" as '\vee_\mathscr{H}';
htmldef "\/H" as
    " <IMG SRC='_bigveeh.gif' WIDTH=23 HEIGHT=19 ALT=' \/H' TITLE='\/H'> ";
  althtmldef "\/H" as ' <FONT SIZE="+1">&or;' +
    '</FONT><SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "\/H" as '\bigvee_\mathscr{H}';
htmldef "0H" as "<IMG SRC='_0h.gif' WIDTH=20 HEIGHT=19 ALT=' 0H' TITLE='0H'>";
  althtmldef "0H" as '0<SUB>&#8459;</SUB>';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "0H" as '0_\mathscr{H}';
htmldef "C_H" as
    " <IMG SRC='_cch.gif' WIDTH=23 HEIGHT=19 ALT=' C_H' TITLE='C_H'> ";
  althtmldef "C_H" as
    ' &#x1D436;<SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "C_H" as 'C_\mathscr{H}';
htmldef "projh" as
    "<IMG SRC='_proj.gif' WIDTH=24 HEIGHT=19 ALT=' proj' TITLE='proj'>" +
    " <IMG SRC='subh.gif' WIDTH=6 HEIGHT=19 ALT='h' TITLE='h'>";
  althtmldef "projh" as 'proj<SUB>&#x210E;</SUB>';
  latexdef "projh" as '\mathrm{proj}_h';
htmldef "0hop" as
    "<IMG SRC='_0hop.gif' WIDTH=28 HEIGHT=19 ALT=' 0hop' TITLE='0hop'>";
  althtmldef "0hop" as ' 0<SUB>hop</SUB> ';
  latexdef "0hop" as "0_\mathrm{hop}";
htmldef "Iop" as
    " <IMG SRC='_iop.gif' WIDTH=18 HEIGHT=19 ALT=' Iop' TITLE='Iop'> ";
  althtmldef "Iop" as ' I<SUB>op</SUB> ';
  latexdef "Iop" as "I_\mathrm{op}";
htmldef "+op" as
    " <IMG SRC='_plop.gif' WIDTH=25 HEIGHT=19 ALT=' +op' TITLE='+op'> ";
  althtmldef "+op" as ' +<SUB>op</SUB> ';
  latexdef "+op" as '+_\mathrm{op}';
htmldef ".op" as
    " <IMG SRC='_cdop.gif' WIDTH=16 HEIGHT=19 ALT=' .op' TITLE='.op'> ";
  althtmldef ".op" as ' <B>&middot;</B><SUB>op</SUB> ';
  latexdef ".op" as '\cdot_\mathrm{op}';
htmldef "-op" as
    " <IMG SRC='_mop.gif' WIDTH=23 HEIGHT=19 ALT=' -op' TITLE='-op'> ";
  althtmldef "-op" as ' &minus;<SUB>op</SUB> ';
  latexdef "-op" as '-_\mathrm{op}';
htmldef "+fn" as
    " <IMG SRC='_plfn.gif' WIDTH=24 HEIGHT=19 ALT=' +fn' TITLE='+fn'> ";
  althtmldef "+fn" as ' +<SUB>fn</SUB> ';
  latexdef "+fn" as '+_\mathrm{fn}';
htmldef ".fn" as
    " <IMG SRC='_cdfn.gif' WIDTH=15 HEIGHT=19 ALT=' .fn' TITLE='.fn'> ";
  althtmldef ".fn" as ' <B>&middot;</B><SUB>fn</SUB> ';
  latexdef ".fn" as '\cdot_\mathrm{fn}';
htmldef "normop" as
  "<IMG SRC='_normsubop.gif' WIDTH=45 HEIGHT=19 ALT=' normop' TITLE='normop'>";
  althtmldef "normop" as 'norm<SUB>op</SUB>';
  latexdef "normop" as '\mathrm{norm}_\mathrm{op}';
htmldef "ContOp" as
    "<IMG SRC='_conop.gif' WIDTH=44 HEIGHT=19 ALT=' ContOp' TITLE='ContOp'>";
  althtmldef "ContOp" as 'ContOp';
  latexdef "ContOp" as '\mathrm{ContOp}';
htmldef "LinOp" as
    "<IMG SRC='_linop.gif' WIDTH=40 HEIGHT=19 ALT=' LinOp' TITLE='LinOp'>";
  althtmldef "LinOp" as 'LinOp';
  latexdef "LinOp" as '\mathrm{LinOp}';
htmldef "BndLinOp" as
    "<IMG SRC='_bndlinop.gif' WIDTH=65 HEIGHT=19 " +
    "ALT=' BndLinOp' TITLE='BndLinOp'>";
  althtmldef "BndLinOp" as 'BndLinOp';
  latexdef "BndLinOp" as '\mathrm{BndLinOp}';
htmldef "UniOp" as
    "<IMG SRC='_uniop.gif' WIDTH=41 HEIGHT=19 ALT=' UniOp' TITLE='UniOp'>";
  althtmldef "UniOp" as 'UniOp';
  latexdef "UniOp" as '\mathrm{UniOp}';
htmldef "HrmOp" as
    "<IMG SRC='_hrmop.gif' WIDTH=47 HEIGHT=19 ALT=' HrmOp' TITLE='HrmOp'>";
  althtmldef "HrmOp" as 'HrmOp';
  latexdef "HrmOp" as '\mathrm{HrmOp}';
htmldef "normfn" as
    "<IMG SRC='_normfn.gif' WIDTH=43 HEIGHT=19 ALT=' normfn' TITLE='normfn'>";
  althtmldef "normfn" as 'norm<SUB>fn</SUB>';
  latexdef "normfn" as '\mathrm{norm}_\mathrm{fn}';
htmldef "null" as
    "<IMG SRC='_null.gif' WIDTH=24 HEIGHT=19 ALT=' null' TITLE='null'>";
  althtmldef "null" as 'null';
  latexdef "null" as '\mathrm{null}';
htmldef "ContFn" as
    "<IMG SRC='_confn.gif' WIDTH=42 HEIGHT=19 ALT=' ContFn' TITLE='ContFn'>";
  althtmldef "ContFn" as 'ContFn';
  latexdef "ContFn" as '\mathrm{ContFn}';
htmldef "LinFn" as
    "<IMG SRC='_linfn.gif' WIDTH=38 HEIGHT=19 ALT=' LinFn' TITLE='LinFn'>";
  althtmldef "LinFn" as 'LinFn';
  latexdef "LinFn" as '\mathrm{LinFn}';
htmldef "adjh" as
    "<IMG SRC='_adjh.gif' WIDTH=26 HEIGHT=19 ALT=' adjh' TITLE='adjh'>";
  althtmldef "adjh" as 'adj<SUB>&#x210E;</SUB>';
  latexdef "adjh" as '\mathrm{adj}_h';
htmldef "bra" as
    "<IMG SRC='_bra.gif' WIDTH=22 HEIGHT=19 ALT=' bra' TITLE='bra'>";
  althtmldef "bra" as 'bra';
  latexdef "bra" as '\mathrm{bra}';
htmldef "ketbra" as
   " <IMG SRC='_ketbra.gif' WIDTH=43 HEIGHT=19 ALT=' ketbra' TITLE='ketbra'> ";
  althtmldef "ketbra" as ' ketbra ';
  latexdef "ketbra" as '\mathrm{ketbra}';
htmldef "<_op" as
   " <IMG SRC='_leop.gif' WIDTH=24 HEIGHT=19 ALT=' <_op' TITLE='<_op'> ";
  althtmldef "<_op" as " &le;<SUB>op</SUB> ";
  latexdef "<_op" as '\le_\mathrm{op}';
htmldef "eigvec" as
    "<IMG SRC='_eigvec.gif' WIDTH=41 HEIGHT=19 ALT=' eigvec' TITLE='eigvec'>";
  althtmldef "eigvec" as 'eigvec';
  latexdef "eigvec" as '\operatorname{eigvec}';
htmldef "eigval" as
    "<IMG SRC='_eigval.gif' WIDTH=39 HEIGHT=19 ALT=' eigval' TITLE='eigval'>";
  althtmldef "eigval" as 'eigval';
  latexdef "eigval" as '\operatorname{eigval}';
htmldef "Lambda" as
    "<IMG SRC='clambda.gif' WIDTH=11 HEIGHT=19 ALT=' Lambda' TITLE='Lambda'>";
  althtmldef "Lambda" as 'Lambda';
  latexdef "Lambda" as '\Lambda';
htmldef "States" as
    "<IMG SRC='_states.gif' WIDTH=40 HEIGHT=19 ALT=' States' TITLE='States'>";
  althtmldef "States" as 'States';
  latexdef "States" as '\mathrm{States}';
    /* These don't have images. */
htmldef "CHStates" as
    "<IMG SRC='_chstates.gif' WIDTH=61 HEIGHT=19 " +
    "ALT=' CHStates' TITLE='CHStates'>";
  althtmldef "CHStates" as 'CHStates';
  latexdef "CHStates" as '\mathrm{CHStates}';
htmldef "HAtoms" as 'HAtoms';
  althtmldef "HAtoms" as 'HAtoms';
  latexdef "HAtoms" as '\mathrm{HAtoms}';
htmldef "<oH" as
    " <IMG SRC='_ldh.gif' WIDTH=25 HEIGHT=19 ALT=' &lt;oH' TITLE='&lt;oH'> ";
  althtmldef "<oH" as
    ' &#8918;<SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "<oH" as '\lessdot_\mathscr{H}';
htmldef "MH" as
    " <IMG SRC='_mh.gif' WIDTH=27 HEIGHT=19 ALT=' MH' TITLE='MH'> ";
  althtmldef "MH" as ' &#x1D440;<SUB>&#8459;</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "MH" as 'M_\mathscr{H}';
htmldef "MH*" as
    " <IMG SRC='_mhast.gif' WIDTH=27 HEIGHT=19 ALT=' MH*' TITLE='MH*'> ";
  althtmldef "MH*" as ' &#x1D440;<SUB>&#8459;</SUB><SUP>*</SUP> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "MH*" as 'M_\mathscr{H}^*';

/* stuff to be sorted into the right places above: */

/* htmldef, althtmldef, latexdef for mathboxes */
/* Note the "Mathbox of" instead of "Mathbox for" to make searching easier. */

/* Mathbox of Thierry Arnoux */
htmldef "class-o" as "class-o";
  althtmldef "class-o" as "class-o";
  latexdef "class-o" as "\mathrm{class-o}";
htmldef "class-n" as "class-n";
  althtmldef "class-n" as "class-n";
  latexdef "class-n" as "\mathrm{class-n}";
htmldef "<<<" as "&lt;&lt;&lt;";
  althtmldef "<<<" as "&#x22D8;";
  latexdef "<<<" as "\mathrm{<<<}";
htmldef "Archi" as "Archi";
  althtmldef "Archi" as "Archi";
  latexdef "Archi" as "\mathrm{Archi}";
htmldef "oMnd" as "oMnd";
  althtmldef "oMnd" as "oMnd";
  latexdef "oMnd" as "\mathrm{oMnd}";
htmldef "oGrp" as "oGrp";
  althtmldef "oGrp" as "oGrp";
  latexdef "oGrp" as "\mathrm{oGrp}";
htmldef "oRing" as "oRing";
  althtmldef "oRing" as "oRing";
  latexdef "oRing" as "\mathrm{oRing}";
htmldef "oField" as "oField";
  althtmldef "oField" as "oField";
  latexdef "oField" as "\mathrm{oField}";
htmldef "toCyc" as "toCyc";
  althtmldef "toCyc" as "toCyc";
  latexdef "toCyc" as "\mathrm{toCyc}";
htmldef "Monot" as "Monot";
  althtmldef "Monot" as "Monot";
  latexdef "Monot" as "\mathrm{Monot}";
htmldef "MGalConn" as "MGalConn";
  althtmldef "MGalConn" as "MGalConn";
  latexdef "MGalConn" as "\mathrm{MGalConn}";
htmldef ".c_" as
    " <IMG SRC='_.le.gif' WIDTH=11 HEIGHT=19 ALT=' .&lt;_' TITLE='.&lt;_'> ";
  althtmldef ".c_" as
    ' <SPAN CLASS=symvar STYLE="border-bottom:1px dotted;color:#C3C">' +
    '&#x2272;</SPAN> ';
  latexdef ".c_" as "\lesssim";
htmldef "SLMod" as "SLMod";
  althtmldef "SLMod" as "SLMod";
  latexdef "SLMod" as "\mathrm{SLMod}";
htmldef "|`v" as " &#8638;<SUB>v</SUB> ";
  althtmldef "|`v" as " &#8638;<SUB>v</SUB> ";
  latexdef "|`v" as "\restriction_v";
htmldef "PrmIdeal" as "PrmIdeal";
  althtmldef "PrmIdeal" as "PrmIdeal";
  latexdef "PrmIdeal" as "\mathrm{PrmIdeal}";
htmldef "MaxIdeal" as "MaxIdeal";
  althtmldef "MaxIdeal" as "MaxIdeal";
  latexdef "MaxIdeal" as "\mathrm{MaxIdeal}";
htmldef "EDomn" as "EDomn";
  althtmldef "EDomn" as "EDomn";
  latexdef "EDomn" as "\mathrm{EDomn}";
htmldef "EuclF" as "EuclF";
  althtmldef "EuclF" as "EuclF";
  latexdef "EuclF" as "\mathrm{EuclF}";
htmldef "UFD" as "UFD";
  althtmldef "UFD" as "UFD";
  latexdef "UFD" as "\mathrm{UFD}";
htmldef "IDLsrg" as "IDLsrg";
  althtmldef "IDLsrg" as "IDLsrg";
  latexdef "IDLsrg" as "\mathrm{IDLsrg}";
htmldef "Spec" as "Spec";
  althtmldef "Spec" as "Spec";
  latexdef "Spec" as "\mathrm{Spec}";
htmldef "subMat1" as "subMat1";
  althtmldef "subMat1" as "subMat1";
  latexdef "subMat1" as "\mathrm{subMat1}";
htmldef "litMat" as "litMat";
  althtmldef "litMat" as "litMat";
  latexdef "litMat" as "\mathrm{litMat}";
htmldef "RRExt" as " &#8477;Ext ";
  althtmldef "RRExt" as " &#8477;Ext ";
  latexdef "RRExt" as "\mathbb{R}\mathrm{Ext}";
htmldef "PsMet" as "PsMet";
  althtmldef "PsMet" as "PsMet";
  latexdef "PsMet" as "\mathrm{PsMet}";
htmldef "~Met" as "~Met";
  althtmldef "~Met" as "~<SUB>Met</SUB>";
  latexdef "~Met" as "~_\mathrm{Met}";
htmldef "pstoMet" as "pstoMet";
  althtmldef "pstoMet" as "pstoMet";
  latexdef "pstoMet" as "\mathrm{pstoMet}";
htmldef "HCmp" as "HCmp";
  althtmldef "HCmp" as "HCmp";
  latexdef "HCmp" as "\mathrm{HCmp}";
htmldef "CnExt" as "CnExt";
  althtmldef "CnExt" as "CnExt";
  latexdef "CnExt" as "\mathrm{CnExt}";
htmldef "UnifOn" as "UnifOn";
  althtmldef "UnifOn" as "UnifOn";
  latexdef "UnifOn" as "\mathrm{UnifOn}";
htmldef "UnifSt" as "UnifSt";
  althtmldef "UnifSt" as "UnifSt";
  latexdef "UnifSt" as "\mathrm{UnifSt}";
htmldef "UnifSp" as "UnifSp";
  althtmldef "UnifSp" as "UnifSp";
  latexdef "UnifSp" as "\mathrm{UnifSp}";
htmldef "toUnifSp" as "toUnifSp";
  althtmldef "toUnifSp" as "toUnifSp";
  latexdef "toUnifSp" as "\mathrm{toUnifSp}";
htmldef "unifTop" as "unifTop";
  althtmldef "unifTop" as "unifTop";
  latexdef "unifTop" as "\mathrm{unifTop}";
htmldef "uCn" as " Cn<SUB>u</SUB>";
  althtmldef "uCn" as " Cn<SUB>u</SUB>";
  latexdef "uCn" as "\mathrm{Cn_u}";
htmldef "CauFilU" as "CauFil<SUB>u</SUB>";
  althtmldef "CauFilU" as "CauFil<SUB>u</SUB>";
  latexdef "CauFilU" as "\mathrm{CauFil_u}";
htmldef "CUnifSp" as "CUnifSp";
  althtmldef "CUnifSp" as "CUnifSp";
  latexdef "CUnifSp" as "\mathrm{CUnifSp}";
htmldef "metUnif" as "metUnif";
  althtmldef "metUnif" as "metUnif";
  latexdef "metUnif" as "\mathrm{metUnif}";
htmldef "CovHasRef" as "CovHasRef";
  althtmldef "CovHasRef" as "CovHasRef";
  latexdef "CovHasRef" as "\mathrm{CovHasRef}";
htmldef "Ldlf" as "Ldlf";
  althtmldef "Ldlf" as "Ldlf";
  latexdef "Ldlf" as "\mathrm{Ldlf}";
htmldef "Paracomp" as "Paracomp";
  althtmldef "Paracomp" as "Paracomp";
  latexdef "Paracomp" as "\mathrm{Paracomp}";
htmldef "ManTop" as "ManTop";
  althtmldef "ManTop" as "ManTop";
  latexdef "ManTop" as "\mathrm{ManTop}";
htmldef "/e" as " /<SUB>&#x1D452;</SUB> ";
  althtmldef "/e" as " /<SUB>&#x1D452;</SUB> ";
  latexdef "/e" as '/_e';
htmldef "sum*" as "&Sigma;<SUP>*</SUP>";
  althtmldef "sum*" as "&Sigma;<SUP>*</SUP>";
  latexdef "sum*" as "\sum^*";
htmldef "sgns" as "sgn<SUB>s</SUB>";
  althtmldef "sgns" as "sgn<SUB>s</SUB>";
  latexdef "sgns" as "\operatorname{sgn_s}";
htmldef "FixPts" as "FixPts";
  althtmldef "FixPts" as "FixPts";
  latexdef "FixPts" as "\mathrm{FixPts}";
htmldef "oFC" as " oFC ";
  althtmldef "oFC" as " &#8728;<SUB>f/c</SUB> ";
  latexdef "oFC" as "\circ_\mathrm{f/c}";
htmldef "seqstr" as "seq<SUB>str</SUB>";
  althtmldef "seqstr" as "seq<SUB>str</SUB>";
  latexdef "seqstr" as "\mathrm{seq_str}";
htmldef "Fibci" as "Fibci";
  althtmldef "Fibci" as "Fibci";
  latexdef "Fibci" as "\mathrm{Fibci}";
htmldef "sigAlgebra" as "sigAlgebra";
  althtmldef "sigAlgebra" as "sigAlgebra";
  latexdef "sigAlgebra" as "\mathrm{sigAlgebra}";
htmldef "sigaGen" as "sigaGen";
  althtmldef "sigaGen" as "sigaGen";
  latexdef "sigaGen" as "\mathrm{sigaGen}";
htmldef "BrSiga" as "&#x1D505;<SUB>&#8477;</SUB>";
  althtmldef "BrSiga" as "&#x1D505;<SUB>&#8477;</SUB>";
  latexdef "BrSiga" as "\mathfrak{B}_\mathbb{R}";
htmldef "sX" as " &times;<SUB>s</SUB> ";
  althtmldef "sX" as " &times;<SUB>s</SUB> ";
  latexdef "sX" as "\times_s";
htmldef "measures" as "measures";
  althtmldef "measures" as "measures";
  latexdef "measures" as "\mathrm{measures}";
htmldef "Ddelta" as "&delta;";
  althtmldef "Ddelta" as "&delta;";
  latexdef "Ddelta" as "\mathrm{\delta}";
htmldef "toOMeas" as "toOMeas";
  althtmldef "toOMeas" as "toOMeas";
  latexdef "toOMeas" as "\mathrm{toOMeas}";
htmldef "toCaraSiga" as "toCaraSiga";
  althtmldef "toCaraSiga" as "toCaraSiga";
  latexdef "toCaraSiga" as "\mathrm{toCaraSiga}";
htmldef "MblFnM" as "MblFnM";
  althtmldef "MblFnM" as "MblFnM";
  latexdef "MblFnM" as "\mathrm{MblFnM}";
htmldef "ae" as "a.e.";
  althtmldef "ae" as "a.e.";
  latexdef "ae" as "\mathrm{a.e.}";
htmldef "~ae" as "~ a.e.";
  althtmldef "~ae" as "~ a.e.";
  latexdef "~ae" as "\mathrm{~ a.e.}";
htmldef "QQHom" as "QQHom";
  althtmldef "QQHom" as "&#8474;Hom";
  latexdef "QQHom" as "\mathbb{Q}\mathrm{Hom}";
htmldef "RRHom" as "RRHom";
  althtmldef "RRHom" as "&#8477;Hom";
  latexdef "RRHom" as "\mathbb{R}\mathrm{Hom}";
htmldef "RR*Hom" as "RR<SUP>*</SUP>Hom";
  althtmldef "RR*Hom" as "&#8477;<SUP>*</SUP>Hom";
  latexdef "RR*Hom" as "\mathbb{R}^*\mathrm{Hom}";
htmldef "itgm" as "itgm";
  althtmldef "itgm" as "itgm";
  latexdef "itgm" as "\mathrm{itgm}";
htmldef "sitg" as "sitg";
  althtmldef "sitg" as "sitg";
  latexdef "sitg" as "\mathrm{sitg}";
htmldef "sitm" as "sitm";
  althtmldef "sitm" as "sitm";
  latexdef "sitm" as "\mathrm{sitm}";
htmldef "Prob" as "Prob";
  althtmldef "Prob" as "Prob";
  latexdef "Prob" as "\mathrm{Prob}";
htmldef "cprob" as "cprob";
  althtmldef "cprob" as "cprob";
  latexdef "cprob" as "\mathrm{cprob}";
htmldef "rRndVar" as "rRndVar";
  althtmldef "rRndVar" as "rRndVar";
  latexdef "rRndVar" as "\mathrm{rRndVar}";
htmldef "oRVC" as "&#8728;<SUB>RV/&#x1D450;</SUB>";
  althtmldef "oRVC" as "&#8728;<SUB>RV/&#x1D450;</SUB>";
  latexdef "oRVC" as "\circ_RV/c";
htmldef "~RL" as " ~<sub><i>RL</i></sub> ";
  althtmldef "~RL" as " ~<sub><i>RL</i></sub> ";
  latexdef "~RL" as " \sim_{RL} ";
htmldef "RLocal" as " RLocal ";
  althtmldef "RLocal" as " RLocal ";
  latexdef "RLocal" as "\mathbin{\operatorname{RLocal}}";
htmldef "Frac" as " Frac ";
  althtmldef "Frac" as " Frac ";
  latexdef "Frac" as "\mathbin{\operatorname{Frac}}";
htmldef "dim" as "dim";
  althtmldef "dim" as "dim";
  latexdef "dim" as "\mathrm{dim}";
htmldef "/FldExt" as "/<SUB>FldExt</SUB>";
  althtmldef "/FldExt" as "/<SUB>FldExt</SUB>";
  latexdef "/FldExt" as "/FldExt";
htmldef "/FinExt" as "/<SUB>FinExt</SUB>";
  althtmldef "/FinExt" as "/<SUB>FinExt</SUB>";
  latexdef "/FinExt" as "/FinExt";
htmldef "/AlgExt" as "/<SUB>AlgExt</SUB>";
  althtmldef "/AlgExt" as "/<SUB>AlgExt</SUB>";
  latexdef "/AlgExt" as "/_AlgExt";
htmldef "[:]" as "[:]";
  althtmldef "[:]" as "[:]";
  latexdef "[:]" as "[:]";
htmldef "fldGen" as " fldGen ";
  althtmldef "fldGen" as " fldGen ";
  latexdef "fldGen" as "\mathbin{\operatorname{fldGen}}";
htmldef "minPoly" as " minPoly ";
  althtmldef "minPoly" as " minPoly ";
  latexdef "minPoly" as "\mathbin{\operatorname{minPoly}}";
htmldef "Constr" as "Constr";
  althtmldef "Constr" as "Constr";
  latexdef "Constr" as "\mathrm{Constr}";
htmldef "SymPoly" as "SymPoly";
  althtmldef "SymPoly" as "SymPoly";
  latexdef "SymPoly" as "\mathrm{SymPoly}";
htmldef "eSymPoly" as "eSymPoly";
  althtmldef "eSymPoly" as "eSymPoly";
  latexdef "eSymPoly" as "\mathrm{eSymPoly}";
htmldef "extendVars" as "extendVars";
  althtmldef "extendVars" as "extendVars";
  latexdef "extendVars" as "\mathrm{extendVars}";
htmldef "repr" as "repr";
  althtmldef "repr" as "repr";
  latexdef "repr" as "\mathrm{repr}";
htmldef "vts" as "vts";
  althtmldef "vts" as "vts";
  latexdef "vts" as "\mathrm{vts}";
htmldef "leftpad" as ' leftpad ';
  althtmldef "leftpad" as ' leftpad ';
  latexdef "leftpad" as "\mathbin{\operatorname{leftpad}}";
htmldef "Itv" as "Itv";
  althtmldef "Itv" as "Itv";
  latexdef "Itv" as "\mathrm{Itv}";
htmldef "LineG" as "LineG";
  althtmldef "LineG" as "LineG";
  latexdef "LineG" as "\mathrm{LineG}";
htmldef "midG" as "midG";
  althtmldef "midG" as "midG";
  latexdef "midG" as "\mathrm{midG}";
htmldef "pInvG" as "pInvG";
  althtmldef "pInvG" as "pInvG";
  latexdef "pInvG" as "\mathrm{pInvG}";
htmldef "lInvG" as "lInvG";
  althtmldef "lInvG" as "lInvG";
  latexdef "lInvG" as "\mathrm{lInvG}";
htmldef "Ismt" as "Ismt";
  althtmldef "Ismt" as "Ismt";
  latexdef "Ismt" as "\mathrm{Ismt}";
htmldef "TarskiG" as "TarskiG";
  althtmldef "TarskiG" as "TarskiG";
  latexdef "TarskiG" as "\mathrm{TarskiG}";
htmldef "TarskiGC" as "TarskiG<SUB>C</SUB>";
  althtmldef "TarskiGC" as "TarskiG<SUB>C</SUB>";
  latexdef "TarskiGC" as "\mathrm{TarskiG_C}";
htmldef "TarskiGB" as "TarskiG<SUB>B</SUB>";
  althtmldef "TarskiGB" as "TarskiG<SUB>B</SUB>";
  latexdef "TarskiGB" as "\mathrm{TarskiG_B}";
htmldef "TarskiGCB" as "TarskiG<SUB>CB</SUB>";
  althtmldef "TarskiGCB" as "TarskiG<SUB>CB</SUB>";
  latexdef "TarskiGCB" as "\mathrm{TarskiG_CB}";
htmldef "TarskiGE" as "TarskiG<SUB>E</SUB>";
  althtmldef "TarskiGE" as "TarskiG<SUB>E</SUB>";
  latexdef "TarskiGE" as "\mathrm{TarskiG_E}";
htmldef "TarskiGDim>=" as "Dim<SUB>TarskiG</SUB>&ge;";
  althtmldef "TarskiGDim>=" as "Dim<SUB>TarskiG</SUB>&ge;";
  latexdef "TarskiGDim>=" as "\mathrm{Dim_TarskiG}\ge";
htmldef "TarskiG2D" as "TarskiG<SUB>2D</SUB>";
  althtmldef "TarskiG2D" as "TarskiG<SUB>2D</SUB>";
  latexdef "TarskiG2D" as "\mathrm{TarskiG_2D}";
htmldef "AFS" as "AFS";
  althtmldef "AFS" as "AFS";
  latexdef "AFS" as "\mathrm{AFS}";
htmldef "cgrG" as "cgrG";
  althtmldef "cgrG" as "cgrG";
  latexdef "cgrG" as "\mathrm{cgrG}";
htmldef "leG" as "&le;G";
  althtmldef "leG" as "&le;G";
  latexdef "leG" as "\le\mathrm{G}";
htmldef "raG" as "&#8735;G"; /* &angrt; fails validator so use its code */
  althtmldef "raG" as "&#8735;G"; /* &angrt; fails validator so use its code */
  latexdef "raG" as "\llcorner\mathrm{G}";
htmldef "perpG" as "&#x27C2;G";
  althtmldef "perpG" as "&#x27C2;G";
  latexdef "perpG" as "\bot\mathrm{G}";
htmldef "hpG" as "hpG";
  althtmldef "hpG" as "hpG";
  latexdef "hpG" as "\mathrm{hpG}";
htmldef "hlG" as "hlG";
  althtmldef "hlG" as "hlG";
  latexdef "hlG" as "\mathrm{hlG}";
htmldef "PlnG" as "PlnG";
  althtmldef "PlnG" as "hlG";
  latexdef "PlnG" as "\mathrm{PlnG}";
htmldef "parlnG" as "parlnG";
  althtmldef "parlnG" as "parlnG";
  latexdef "parlnG" as "\mathrm{parlnG}";
htmldef "inA" as "inA";
  althtmldef "inA" as "inA";
  latexdef "inA" as "\mathrm{inA}";
htmldef "leA" as "&le;<SUB>&angle;</SUB>";
  althtmldef "leA" as "&le;<SUB>&angle;</SUB>";
  latexdef "leA" as "\le_\angle";
htmldef "cgrA" as "cgrA";
  althtmldef "cgrA" as "cgrA";
  latexdef "cgrA" as "\mathrm{cgrA}";
htmldef "eqltrG" as "eqltrG";
  althtmldef "eqltrG" as "eqltrG";
  latexdef "eqltrG" as "\mathrm{eqltrG}";
htmldef "EEG" as "EEG";
  althtmldef "EEG" as "EEG";
  latexdef "EEG" as "\mathrm{EEG}";
htmldef "toTG" as "toTG";
  althtmldef "toTG" as "toTG";
  latexdef "toTG" as "\mathrm{toTG}";
/* End of Thierry Arnoux's mathbox */

/* Mathbox of BTernaryTau */
htmldef "kard" as "kard";
  althtmldef "kard" as "kard";
  latexdef "kard" as "\mathrm{kard}";
htmldef "AcyclicGraph" as "AcyclicGraph";
  althtmldef "AcyclicGraph" as "AcyclicGraph";
  latexdef "AcyclicGraph" as "\mathrm{AcyclicGraph}";
/* End of BTernaryTau's mathbox */

/* Mathbox of Mario Carneiro */
htmldef "zeta" as
    "<IMG SRC='zeta.gif' WIDTH=9 HEIGHT=19 ALT=' zeta' TITLE='zeta'>";
  althtmldef "zeta" as "&zeta;";
  latexdef "zeta" as "\zeta";
htmldef "_G" as
    "<IMG SRC='cgamma.gif' WIDTH=10 HEIGHT=19 ALT=' _G' TITLE='_G'>";
  althtmldef "_G" as "&Gamma;";
  latexdef "_G" as "\Gamma";
htmldef "log_G" as
    "<IMG SRC='_log.gif' WIDTH=20 HEIGHT=19 ALT=' log' TITLE='log'> " +
    "<IMG SRC='cgamma.gif' WIDTH=10 HEIGHT=19 ALT='_G' TITLE='_G'>";
  althtmldef "log_G" as "log &Gamma;";
  latexdef "log_G" as "\log\Gamma";
htmldef "1/_G" as
    "1/<IMG SRC='cgamma.gif' WIDTH=10 HEIGHT=19 ALT=' _G' TITLE='_G'>";
  althtmldef "1/_G" as "1/&Gamma;";
  latexdef "1/_G" as "1/\Gamma";
htmldef "Retr" as " Retr ";
  althtmldef "Retr" as " Retr ";
  latexdef "Retr" as "\mathrm{Retr}";
htmldef "PConn" as "PConn";
  althtmldef "PConn" as "PConn";
  latexdef "PConn" as " \mathrm{PConn} ";
htmldef "SConn" as "SConn";
  althtmldef "SConn" as "SConn";
  latexdef "SConn" as "\mathrm{SConn}";
htmldef "CovMap" as " CovMap ";
  althtmldef "CovMap" as " CovMap ";
  latexdef "CovMap" as " \mathrm{CovMap} ";
htmldef "e.g" as
    " <IMG SRC='_ing.gif' WIDTH=17 HEIGHT=19 ALT=' e.g' TITLE='e.g'> ";
  althtmldef "e.g" as "&isin;<SUB>&#x1D454;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "e.g" as "\in_g";
htmldef "|g" as
    " <IMG SRC='barwedge.gif' WIDTH=9 HEIGHT=19 ALT=' |' TITLE='|'>" +
    "<IMG SRC='subg.gif' WIDTH=7 HEIGHT=19 ALT='g' TITLE='g'> ";
  althtmldef "|g" as "&#8892;<SUB>&#x1D454;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "|g" as "\barwedge_g";
htmldef "A.g" as
    "<IMG SRC='_forallg.gif' WIDTH=14 HEIGHT=19 ALT=' A.g' TITLE='A.g'>";
  althtmldef "A.g" as
    "&forall;<SUB>&#x1D454;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "A.g" as "\forall_g";
htmldef "=g" as
    " <IMG SRC='_eqg.gif' WIDTH=19 HEIGHT=19 ALT=' =g' TITLE='=g'> ";
  althtmldef "=g" as "=<SUB>&#x1D454;</SUB>";
  latexdef "=g" as "=_g";
htmldef "/\g" as
    " <IMG SRC='_wedgeg.gif' WIDTH=18 HEIGHT=19 ALT=' /\g' TITLE='/\g'> ";
  althtmldef "/\g" as "&and;<SUB>&#x1D454;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "/\g" as "\wedge_g";
htmldef "-.g" as
    "<IMG SRC='_lnotg.gif' WIDTH=17 HEIGHT=19 ALT=' -.g' TITLE='-.g'>";
  althtmldef "-.g" as "&not;<SUB>&#x1D454;</SUB>";
  latexdef "-.g" as "\lnot_g";
htmldef "->g" as
    " <IMG SRC='_tog.gif' WIDTH=20 HEIGHT=19 ALT=' -&gt;g' TITLE='-&gt;g'> ";
  althtmldef "->g" as
    " &rarr;<SUB>&#x1D454;</SUB> ";
  latexdef "->g" as "\to_g";
htmldef "<->g" as " <IMG SRC='_lrarrg.gif' WIDTH=20 HEIGHT=19 " +
    "ALT=' &lt;-&gt;g' TITLE='&lt;-&gt;g'> ";
  althtmldef "<->g" as " &harr;<SUB>&#x1D454;</SUB> ";
  latexdef "<->g" as "\leftrightarrow_g";
htmldef "\/g" as
    " <IMG SRC='_veeg.gif' WIDTH=15 HEIGHT=19 ALT=' \/g' TITLE='\/g'> ";
  althtmldef "\/g" as " &or;<SUB>&#x1D454;</SUB> ";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "\/g" as "\vee_g";
htmldef "E.g" as
    "<IMG SRC='_existsg.gif' WIDTH=16 HEIGHT=19 ALT=' E.g' TITLE='E.g'>";
  althtmldef "E.g" as
    "&exist;<SUB>&#x1D454;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "E.g" as "\exists_g";
htmldef "Fmla" as
    "<IMG SRC='_fmla.gif' WIDTH=33 HEIGHT=19 ALT=' Fmla' TITLE='Fmla'>";
  althtmldef "Fmla" as "Fmla";
  latexdef "Fmla" as "\mathrm{Fmla}";
htmldef "Sat" as
    " <IMG SRC='_sat.gif' WIDTH=22 HEIGHT=19 ALT=' Sat' TITLE='Sat'> ";
  althtmldef "Sat" as " Sat ";
  latexdef "Sat" as "\mathrm{Sat}";
htmldef "SatE" as
    " <IMG SRC='_sat.gif' WIDTH=22 HEIGHT=19 ALT=' Sat' TITLE='Sat'>" +
    "<IMG SRC='subin.gif' WIDTH=7 HEIGHT=19 ALT='E' TITLE='E'> ";
  althtmldef "SatE" as " Sat<SUB>&isin;</SUB> ";
  latexdef "SatE" as "\mathrm{Sat}_\in";
htmldef "|=" as
    " <IMG SRC='models.gif' WIDTH=12 HEIGHT=19 ALT=' |=' TITLE='|='> ";
  althtmldef "|=" as "&#8871;";
  latexdef "|=" as "\models";
htmldef "AxExt" as
    "<IMG SRC='_axext.gif' WIDTH=41 HEIGHT=19 ALT=' AxExt' TITLE='AxExt'>";
  althtmldef "AxExt" as "AxExt";
  latexdef "AxExt" as "\mathrm{AxExt}";
htmldef "AxRep" as
    "<IMG SRC='_axrep.gif' WIDTH=43 HEIGHT=19 ALT=' AxRep' TITLE='AxRep'>";
  althtmldef "AxRep" as "AxRep";
  latexdef "AxRep" as "\mathrm{AxRep}";
htmldef "AxPow" as
    "<IMG SRC='_axpow.gif' WIDTH=46 HEIGHT=19 ALT=' AxPow' TITLE='AxPow'>";
  althtmldef "AxPow" as "AxPow";
  latexdef "AxPow" as "\mathrm{AxPow}";
htmldef "AxUn" as
    "<IMG SRC='_axun.gif' WIDTH=36 HEIGHT=19 ALT=' AxUn' TITLE='AxUn'>";
  althtmldef "AxUn" as "AxUn";
  latexdef "AxUn" as "\mathrm{AxUn}";
htmldef "AxReg" as
    "<IMG SRC='_axreg.gif' WIDTH=43 HEIGHT=19 ALT=' AxReg' TITLE='AxReg'>";
  althtmldef "AxReg" as "AxReg";
  latexdef "AxReg" as "\mathrm{AxReg}";
htmldef "AxInf" as
    "<IMG SRC='_axinf.gif' WIDTH=36 HEIGHT=19 ALT=' AxInf' TITLE='AxInf'>";
  althtmldef "AxInf" as "AxInf";
  latexdef "AxInf" as "\mathrm{AxInf}";
htmldef "ZF" as
    "<IMG SRC='_zf.gif' WIDTH=19 HEIGHT=19 ALT=' ZF' TITLE='ZF'>";
  althtmldef "ZF" as "<FONT FACE=sans-serif><B>ZF</B></FONT>";
  latexdef "ZF" as "\mathsf{ZF}";
htmldef "mCN" as "mCN";
  althtmldef "mCN" as "mCN";
  latexdef "mCN" as "\mathrm{mCN}";
htmldef "mVR" as "mVR";
  althtmldef "mVR" as "mVR";
  latexdef "mVR" as "\mathrm{mVR}";
htmldef "mType" as "mType";
  althtmldef "mType" as "mType";
  latexdef "mType" as "\mathrm{mType}";
htmldef "mVT" as "mVT";
  althtmldef "mVT" as "mVT";
  latexdef "mVT" as "\mathrm{mVT}";
htmldef "mTC" as "mTC";
  althtmldef "mTC" as "mTC";
  latexdef "mTC" as "\mathrm{mTC}";
htmldef "mAx" as "mAx";
  althtmldef "mAx" as "mAx";
  latexdef "mAx" as "\mathrm{mAx}";
htmldef "mREx" as "mREx";
  althtmldef "mREx" as "mREx";
  latexdef "mREx" as "\mathrm{mREx}";
htmldef "mEx" as "mEx";
  althtmldef "mEx" as "mEx";
  latexdef "mEx" as "\mathrm{mEx}";
htmldef "mDV" as "mDV";
  althtmldef "mDV" as "mDV";
  latexdef "mDV" as "\mathrm{mDV}";
htmldef "mVars" as "mVars";
  althtmldef "mVars" as "mVars";
  latexdef "mVars" as "\mathrm{mVars}";
htmldef "mRSubst" as "mRSubst";
  althtmldef "mRSubst" as "mRSubst";
  latexdef "mRSubst" as "\mathrm{mRSubst}";
htmldef "mSubst" as "mSubst";
  althtmldef "mSubst" as "mSubst";
  latexdef "mSubst" as "\mathrm{mSubst}";
htmldef "mVH" as "mVH";
  althtmldef "mVH" as "mVH";
  latexdef "mVH" as "\mathrm{mVH}";
htmldef "mPreSt" as "mPreSt";
  althtmldef "mPreSt" as "mPreSt";
  latexdef "mPreSt" as "\mathrm{mPreSt}";
htmldef "mStRed" as "mStRed";
  althtmldef "mStRed" as "mStRed";
  latexdef "mStRed" as "\mathrm{mStRed}";
htmldef "mStat" as "mStat";
  althtmldef "mStat" as "mStat";
  latexdef "mStat" as "\mathrm{mStat}";
htmldef "mFS" as "mFS";
  althtmldef "mFS" as "mFS";
  latexdef "mFS" as "\mathrm{mFS}";
htmldef "mCls" as "mCls";
  althtmldef "mCls" as "mCls";
  latexdef "mCls" as "\mathrm{mCls}";
htmldef "mPPSt" as "mPPSt";
  althtmldef "mPPSt" as "mPPSt";
  latexdef "mPPSt" as "\mathrm{mPPSt}";
htmldef "mThm" as "mThm";
  althtmldef "mThm" as "mThm";
  latexdef "mThm" as "\mathrm{mThm}";
htmldef "m0St" as "m0St";
  althtmldef "m0St" as "m0St";
  latexdef "m0St" as "\mathrm{m0St}";
htmldef "mSA" as "mSA";
  althtmldef "mSA" as "mSA";
  latexdef "mSA" as "\mathrm{mSA}";
htmldef "mWGFS" as "mWGFS";
  althtmldef "mWGFS" as "mWGFS";
  latexdef "mWGFS" as "\mathrm{mWGFS}";
htmldef "mSyn" as "mSyn";
  althtmldef "mSyn" as "mSyn";
  latexdef "mSyn" as "\mathrm{mSyn}";
htmldef "mESyn" as "mESyn";
  althtmldef "mESyn" as "mESyn";
  latexdef "mESyn" as "\mathrm{mESyn}";
htmldef "mGFS" as "mGFS";
  althtmldef "mGFS" as "mGFS";
  latexdef "mGFS" as "\mathrm{mGFS}";
htmldef "mTree" as "mTree";
  althtmldef "mTree" as "mTree";
  latexdef "mTree" as "\mathrm{mTree}";
htmldef "mST" as "mST";
  althtmldef "mST" as "mST";
  latexdef "mST" as "\mathrm{mST}";
htmldef "mSAX" as "mSAX";
  althtmldef "mSAX" as "mSAX";
  latexdef "mSAX" as "\mathrm{mSAX}";
htmldef "mUFS" as "mUFS";
  althtmldef "mUFS" as "mUFS";
  latexdef "mUFS" as "\mathrm{mUFS}";
htmldef "mUV" as "mUV";
  althtmldef "mUV" as "mUV";
  latexdef "mUV" as "\mathrm{mUV}";
htmldef "mVL" as "mVL";
  althtmldef "mVL" as "mVL";
  latexdef "mVL" as "\mathrm{mVL}";
htmldef "mVSubst" as "mVSubst";
  althtmldef "mVSubst" as "mVSubst";
  latexdef "mVSubst" as "\mathrm{mVSubst}";
htmldef "mFresh" as "mFresh";
  althtmldef "mFresh" as "mFresh";
  latexdef "mFresh" as "\mathrm{mFresh}";
htmldef "mFRel" as "mFRel";
  althtmldef "mFRel" as "mFRel";
  latexdef "mFRel" as "\mathrm{mFRel}";
htmldef "mEval" as "mEval";
  althtmldef "mEval" as "mEval";
  latexdef "mEval" as "\mathrm{mEval}";
htmldef "mMdl" as "mMdl";
  althtmldef "mMdl" as "mMdl";
  latexdef "mMdl" as "\mathrm{mMdl}";
htmldef "mUSyn" as "mUSyn";
  althtmldef "mUSyn" as "mUSyn";
  latexdef "mUSyn" as "\mathrm{mUSyn}";
htmldef "mGMdl" as "mGMdl";
  althtmldef "mGMdl" as "mGMdl";
  latexdef "mGMdl" as "\mathrm{mGMdl}";
htmldef "mItp" as "mItp";
  althtmldef "mItp" as "mItp";
  latexdef "mItp" as "\mathrm{mItp}";
htmldef "mFromItp" as "mFromItp";
  althtmldef "mFromItp" as "mFromItp";
  latexdef "mFromItp" as "\mathrm{mFromItp}";
htmldef "IntgRing" as " IntgRing ";
  althtmldef "IntgRing" as " IntgRing ";
  latexdef "IntgRing" as "\mathrm{IntgRing}";
htmldef "cplMetSp" as " cplMetSp ";
  althtmldef "cplMetSp" as " cplMetSp ";
  latexdef "cplMetSp" as "\mathrm{cplMetSp}";
htmldef "HomLimB" as " HomLimB ";
  althtmldef "HomLimB" as " HomLimB ";
  latexdef "HomLimB" as "\mathrm{HomLimB}";
htmldef "HomLim" as " HomLim ";
  althtmldef "HomLim" as " HomLim ";
  latexdef "HomLim" as "\mathrm{HomLim}";
htmldef "polyFld" as " polyFld ";
  althtmldef "polyFld" as " polyFld ";
  latexdef "polyFld" as "\mathrm{polyFld}";
htmldef "splitFld1" as " splitFld<sub>1</sub> ";
  althtmldef "splitFld1" as " splitFld<sub>1</sub> ";
  latexdef "splitFld1" as "\mathrm{splitFld}_1";
htmldef "splitFld" as " splitFld ";
  althtmldef "splitFld" as " splitFld ";
  latexdef "splitFld" as "\mathrm{splitFld}";
htmldef "polySplitLim" as " polySplitLim ";
  althtmldef "polySplitLim" as " polySplitLim ";
  latexdef "polySplitLim" as "\mathrm{polySplitLim}";
htmldef "ZRing" as "ZRing";
  althtmldef "ZRing" as "ZRing";
  latexdef "ZRing" as "\mathrm{ZRing}";
htmldef "GF" as " GF ";
  althtmldef "GF" as " GF ";
  latexdef "GF" as "\mathrm{GF}";
htmldef "GF_oo" as "GF<sub>&infin;</sub>";
  althtmldef "GF_oo" as "GF<sub>&infin;</sub>";
  latexdef "GF_oo" as "\mathrm{GF}_\infty";
htmldef "~Qp" as "~Qp";
  althtmldef "~Qp" as "~Qp";
  latexdef "~Qp" as "\sim_{\mathbb{Q}_p}";
htmldef "/Qp" as "/Qp";
  althtmldef "/Qp" as "/Qp";
  latexdef "/Qp" as "/_{\mathbb{Q}_p}";
htmldef "Qp" as "Qp";
  althtmldef "Qp" as "Qp";
  latexdef "Qp" as "\mathbb{Q}_p";
htmldef "Zp" as "Zp";
  althtmldef "Zp" as "Zp";
  latexdef "Zp" as "\mathbb{Z}_p";
htmldef "_Qp" as "_Qp";
  althtmldef "_Qp" as "_Qp";
  latexdef "_Qp" as "\overline{\mathbb{Q}_p}";
htmldef "Cp" as "Cp";
  althtmldef "Cp" as "Cp";
  latexdef "Cp" as "\mathbb{C}_p";
/* End of Mario Carneiro's mathbox */

/* Mathbox of Paul Chapman */
/* End of Paul Chapman's mathbox */

/* Mathbox of Drahflow */
htmldef "^r" as
    " <IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 ALT='^' TITLE='^'>" +
    "<IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 ALT='r' TITLE='r'> " ;
  althtmldef "^r" as '&uarr;<sub>&#x1D45F;</sub>';
  latexdef "^r" as "\uparrow_r";
htmldef "t*rec" as "<IMG SRC='t.gif' WIDTH=7 HEIGHT=19 ALT=' t' TITLE='t'>" +
    "<IMG SRC='ast.gif' WIDTH=7 HEIGHT=19 ALT='*' TITLE='*'>" + "rec";
  althtmldef "t*rec" as "t*rec";
  latexdef "t*rec" as "\mathrm{t}*_\mathrm{rec}";
/* End of Drahflow's mathbox */

/* Mathbox of Adrian Ducourtial */
htmldef "CloneOp" as
    "CloneOp";
  althtmldef "CloneOp" as "CloneOp";
  latexdef "CloneOp" as "\mathrm{CloneOp}";
htmldef "prj" as
    "prj";
  althtmldef "prj" as "prj";
  latexdef "prj" as "\mathrm{prj}";
htmldef "suppos" as
    "suppos";
  althtmldef "suppos" as "suppos";
  latexdef "suppos" as "\mathrm{suppos}";
/* End of Adrian Ducourtial's mathbox */

/* Mathbox of Scott Fenton */
htmldef "Pred" as
    "<IMG SRC='_pred.gif' WIDTH=30 HEIGHT=19 ALT=' Pred' TITLE='Pred'>";
  althtmldef "Pred" as "Pred";
  latexdef "Pred" as "\mathrm{Pred}";
htmldef "t++" as "<IMG SRC='t.gif' WIDTH=7 HEIGHT=19 ALT=' t' TITLE='t'>" +
    "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT='+' TITLE='+'>" +
    "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT='+' TITLE='+'>";
  althtmldef "t++" as "t++";
  latexdef "t++" as "\mathrm{t}++";
htmldef "wrecs" as "wrecs";
  althtmldef "wrecs" as "wrecs";
  latexdef "wrecs" as "\mathrm{wrecs}";
htmldef "wsuc" as "wsuc";
  althtmldef "wsuc" as "wsuc";
  latexdef "wsuc" as "\mathrm{wsuc}";
htmldef "WLim" as "WLim";
  althtmldef "WLim" as "WLim";
  latexdef "WLim" as "\mathrm{WLim}";
htmldef "frecs" as "frecs";
  althtmldef "frecs" as "frecs";
  latexdef "frecs" as "\mathrm{frecs}";

htmldef "+no" as " +no ";
  althtmldef "+no" as " +no ";
  latexdef "+no" as " +_\mathrm{no} ";
htmldef ".no" as
    " <IMG SRC='cdot.gif' WIDTH=4 HEIGHT=19 ALT=' .no' TITLE='.no'>" +
    "<SUB>no</SUB> ";
  althtmldef ".no" as ' &middot;<SUB>no</SUB> '; /* unicode: &#xb7; */
  latexdef ".no" as "\cdot_\mathrm{no}";
htmldef "No" as "<IMG SRC='_no.gif' WIDTH=17 HEIGHT=19 ALT=' No' TITLE='No'>";
  althtmldef "No" as '<FONT FACE=sans-serif> No </FONT>';
  latexdef "No" as "\mathrm{No}";
htmldef "<s" as
    "<IMG SRC='lt.gif' WIDTH=11 HEIGHT=19 ALT=' &lt;' TITLE='&lt;'>" +
    "<IMG SRC='subs.gif' WIDTH=6 HEIGHT=19 ALT='s' TITLE='s'>";
  althtmldef "<s" as " &lt;s ";
  latexdef "<s" as "<_s";
htmldef "bday" as
    "<IMG SRC='_bday.gif' WIDTH=32 HEIGHT=19 ALT=' bday' TITLE='bday'>";
  althtmldef "bday" as '<FONT FACE=sans-serif> bday </FONT>';
  latexdef "bday" as "\mathrm{bday}";
htmldef "<<s" as
    "<IMG SRC='lt.gif' WIDTH=11 HEIGHT=19 ALT=' &lt;' TITLE='&lt;'>" +
    "<IMG SRC='lt.gif' WIDTH=11 HEIGHT=19 ALT=' &lt;' TITLE='&lt;'>" +
    "<IMG SRC='subs.gif' WIDTH=6 HEIGHT=19 ALT='s' TITLE='s'>";
  althtmldef "<<s" as " &lt;&lt;s ";
  latexdef "<<s" as "<<_s";
htmldef "<_s" as
    "<IMG SRC='le.gif' WIDTH=11 HEIGHT=19 ALT=' &le;' TITLE='&le;'>" +
    "<IMG SRC='subs.gif' WIDTH=6 HEIGHT=19 ALT='s' TITLE='s'>";
  althtmldef "<_s" as " &le;s ";
  latexdef "<_s" as "\le_s";
htmldef "|s" as
    "<IMG SRC='vert.gif' WIDTH=3 HEIGHT=19 ALT=' |' TITLE='|'>" +
    "<IMG SRC='subs.gif' WIDTH=6 HEIGHT=19 ALT='s' TITLE='s'>";
  althtmldef "|s" as " |s ";
  latexdef "|s" as "|_s";
htmldef "_Made" as " M ";
  althtmldef "_Made" as " M ";
  latexdef "_Made" as "\mathrm{M}";
htmldef "_Old" as " O ";
  althtmldef "_Old" as " O ";
  latexdef "_Old" as "\mathrm{O}";
htmldef "_New" as " N ";
  althtmldef "_New" as " N ";
  latexdef "_New" as "\mathrm{N}";
htmldef "_Left" as " L ";
  althtmldef "_Left" as " L ";
  latexdef "_Left" as "\mathrm{L}";
htmldef "_Right" as " R ";
  althtmldef "_Right" as " R ";
  latexdef "_Right" as "\mathrm{R}";
htmldef "0s" as " 0<SUB>s</SUB> ";
  althtmldef "0s" as " 0<SUB>s</SUB> ";
  latexdef "0s" as " 0_\mathrm{s} ";
htmldef "1s" as " 1<SUB>s</SUB> ";
  althtmldef "1s" as " 1<SUB>s</SUB> ";
  latexdef "1s" as " 1_\mathrm{s} ";
htmldef "norec" as " norec ";
  althtmldef "norec" as " norec ";
  latexdef "norec" as "\mathrm{norec}";
htmldef "norec2" as " norec2 ";
  althtmldef "norec2" as " norec2 ";
  latexdef "norec2" as "\mathrm{norec2}";
htmldef "+s" as " +<SUB>s</SUB> ";
  althtmldef "+s" as " +<SUB>s</SUB> ";
  latexdef "+s" as " +_\mathrm{s} ";
htmldef "-us" as " -u<SUB>s</SUB> ";
  althtmldef "-us" as " -u<SUB>s</SUB> ";
  latexdef "-us" as " -~\mathrm{u}_\mathrm{s} ";
htmldef "-s" as " -<SUB>s</SUB> ";
  althtmldef "-s" as " -<SUB>s</SUB> ";
  latexdef "-s" as " -_\mathrm{s} ";
htmldef "x.s" as
    " <IMG SRC='cdot.gif' WIDTH=4 HEIGHT=19 ALT=' x.s' TITLE='x.s'>" +
    "<SUB>s</SUB> ";
  althtmldef "x.s" as ' &middot;<SUB>s</SUB> '; /* unicode: &#xb7; */
  latexdef "x.s" as "\cdot_\mathrm{s}";
htmldef "/su" as
    " <IMG SRC='solidus.gif' WIDTH=6 HEIGHT=19 ALT=' /su' TITLE='/su'> " +
    "<SUB>su</SUB>";
  althtmldef "/su" as ' &sol;<SUB>su</SUB> ';
  latexdef "/su" as "/_\mathrm{su}";
htmldef "abs_s" as
    "<IMG SRC='_abs.gif' WIDTH=22 HEIGHT=19 ALT=' abs' TITLE='abs'>" +
    "<SUB>s</SUB>";
  althtmldef "abs_s" as 'abs<SUB>s</SUB>';
  latexdef "abs_s" as "\operatorname{abs}_\mathrm{s}";
htmldef "On_s" as "<IMG SRC='_on.gif' WIDTH=20 HEIGHT=19 ALT=' On_s' " +
  "TITLE='On_s'><SUB>s</SUB>";
  althtmldef "On_s" as 'On<SUB>s</SUB>';
  latexdef "On_s" as "\mathrm{On}_\mathrm{s}";
htmldef "seq_s" as " <IMG SRC='_seq.gif' WIDTH=22 HEIGHT=19 ALT=' seq' " +
    "TITLE='seq'><SUB>s</SUB>";
  althtmldef "seq_s" as 'seq<SUB>s</SUB>';
  latexdef "seq_s" as "\mathrm{seq}_\mathrm{s}";
htmldef "NN0_s" as
  "<IMG SRC='_bbn0.gif' WIDTH=12 HEIGHT=19 ALT=' NN0_s' TITLE='NN0_s'>" +
  "<SUB>s</SUB>";
  althtmldef "NN0_s" as '&#8469;<SUB>0s</SUB>';
  latexdef "NN0_s" as "\mathbb{N}_{0\mathrm{s}}";
htmldef "NN_s" as
  "<IMG SRC='bbn.gif' WIDTH=12 HEIGHT=19 ALT=' NN_s' TITLE='NN_s'>" +
  "<SUB>s</SUB>";
  althtmldef "NN_s" as '&#8469;<SUB>s</SUB>';
  latexdef "NN_s" as "\mathbb{N}_\mathrm{s}";
htmldef "ZZ_s" as
  "<IMG SRC='bbz.gif' WIDTH=11 HEIGHT=19 ALT=' ZZ' TITLE='ZZ'><SUB>s</SUB>";
  althtmldef "ZZ_s" as '&#8484;<SUB>s</SUB>';
  latexdef "ZZ_s" as "\mathbb{Z}_\mathrm{s}";
htmldef "2s" as
  "<IMG SRC='2.gif' WIDTH=8 HEIGHT=19 ALT=' 2' TITLE='2'><SUB>s</SUB>";
  althtmldef "2s" as '2<SUB>s</SUB>';
  latexdef "2s" as "2_\mathrm{s}";
htmldef "^su" as
  "<IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 ALT=' ^' TITLE='^'><SUB>s</SUB>";
  althtmldef "^su" as '&uarr;<SUB>s</SUB>';
  latexdef "^su" as "\uparrow_\mathrm{s}";
htmldef "ZZ_s[1/2]" as
    "<IMG SRC='bbz.gif' WIDTH=11 HEIGHT=19 ALT=' ZZ' TITLE='ZZ'>" +
    "<SUB>s</SUB>" +
    "<IMG SRC='lbrack.gif' WIDTH=5 HEIGHT=19 ALT='[' TITLE='['>" +
    "1/2" +
    "<IMG SRC='rbrack.gif' WIDTH=5 HEIGHT=19 ALT=']' TITLE=']'>";
althtmldef "ZZ_s[1/2]" as '&#8484;<SUB>s</SUB>[1/2]';
latexdef "ZZ_s[1/2]" as "\mathbb{Z}_{\mathrm{s}}[\frac{1}{2}]";
htmldef "RR_s" as
  "<IMG SRC='bbr.gif' WIDTH=13 HEIGHT=19 ALT=' RR' TITLE='RR'><SUB>s</SUB>";
  althtmldef "RR_s" as '&#8477;<SUB>s</SUB>';
  latexdef "RR_s" as "\mathbb{R}_\mathrm{s}";
htmldef "xO" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D465;<SUB>&#x1D442;</SUB></SPAN>';
  althtmldef "xO" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D465;<SUB>&#x1D442;</SUB></SPAN>';
  latexdef "xO" as "x_O";
htmldef "xL" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D465;<SUB>&#x1D43F;</SUB></SPAN>';
  althtmldef "xL" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D465;<SUB>&#x1D43F;</SUB></SPAN>';
  latexdef "xL" as "x_L";
htmldef "xR" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D465;<SUB>&#x1D445;</SUB></SPAN>';
  althtmldef "xR" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D465;<SUB>&#x1D445;</SUB></SPAN>';
  latexdef "xR" as "x_R";
htmldef "yO" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D466;<SUB>&#x1D442;</SUB></SPAN>';
  althtmldef "yO" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D466;<SUB>&#x1D442;</SUB></SPAN>';
  latexdef "yO" as "y_O";
htmldef "yL" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D466;<SUB>&#x1D43F;</SUB></SPAN>';
  althtmldef "yL" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D466;<SUB>&#x1D43F</SUB></SPAN>';
  latexdef "yL" as "y_L";
htmldef "yR" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D466;<SUB>&#x1D445;</SUB></SPAN>';
  althtmldef "yR" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D466;<SUB>&#x1D445;</SUB></SPAN>';
  latexdef "yR" as "y_R";
htmldef "zO" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D467;<SUB>&#x1D442;</SUB></SPAN>';
  althtmldef "zO" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D467;<SUB>&#x1D442;</SUB></SPAN>';
  latexdef "zO" as "z_O";
htmldef "zL" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D467;<SUB>&#x1D43F;</SUB></SPAN>';
  althtmldef "zL" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D467;<SUB>&#x1D43F;</SUB></SPAN>';
  latexdef "zL" as "z_L";
htmldef "zR" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D467;<SUB>&#x1D445;</SUB></SPAN>';
  althtmldef "zR" as
  '<SPAN CLASS=setvar STYLE="color:red">&#x1D467;<SUB>&#x1D445;</SUB></SPAN>';
  latexdef "zR" as "z_R";
htmldef "al" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D6FB;</SPAN>';
  althtmldef "al" as '<SPAN CLASS=wff STYLE="color:blue">&#x1D6FB;</SPAN>';
  latexdef "al" as "\alpha";
htmldef "/_\" as
    " <IMG SRC='bigtriangleup.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' /_\' TITLE='/_\'> ";
  althtmldef "/_\" as " &#x25b3; ";
  latexdef "/_\" as "\triangle";
htmldef "(x)" as
    " <IMG SRC='otimes.gif' WIDTH=13 HEIGHT=19 ALT=' (x)' TITLE='(x)'> ";
  althtmldef "(x)" as " &#x2297; ";
  latexdef "(x)" as "\otimes";
/*
htmldef "(+)" as
    " <IMG SRC='oplus.gif' WIDTH=13 HEIGHT=19 ALT=' (+)' TITLE='(+)'> ";
  althtmldef "(+)" as " &#x2295; ";
  latexdef "(+)" as "\oplus";
*/
htmldef "Bigcup" as
    "<IMG SRC='_bigcup.gif' WIDTH=44 HEIGHT=19 ALT=' Bigcup' TITLE='Bigcup'>";
  althtmldef "Bigcup" as '<FONT FACE=sans-serif> Bigcup </FONT>';
  latexdef "Bigcup" as "\mathrm{Bigcup}";
htmldef "SSet" as
    "<IMG SRC='_sset.gif' WIDTH=29 HEIGHT=19 ALT=' SSet' TITLE='SSet'>";
  althtmldef "SSet" as '<FONT FACE=sans-serif> SSet </FONT>';
  latexdef "SSet" as "\mathrm{SSet}";
htmldef "Trans" as
    "<IMG SRC='_trans.gif' WIDTH=38 HEIGHT=19 ALT=' Trans' TITLE='Trans'>";
  althtmldef "Trans" as '<FONT FACE=sans-serif> Trans </FONT>';
  latexdef "Trans" as "\mathrm{Trans}";
htmldef "Limits" as
    "<IMG SRC='_limits.gif' WIDTH=41 HEIGHT=19 ALT=' Limits' TITLE='Limits'>";
  althtmldef "Limits" as '<FONT FACE=sans-serif> Limits </FONT>';
  latexdef "Limits" as "\mathrm{Limits}";
htmldef "Fix" as
    "<IMG SRC='_fix.gif' WIDTH=21 HEIGHT=19 ALT=' Fix' TITLE='Fix'>";
  althtmldef "Fix" as '<FONT FACE=sans-serif> Fix </FONT>';
  latexdef "Fix" as "\mathrm{Fix}";
htmldef "Funs" as
    "<IMG SRC='_funs.gif' WIDTH=31 HEIGHT=19 ALT=' Funs' TITLE='Funs'>";
  althtmldef "Funs" as '<FONT FACE=sans-serif> Funs </FONT>';
  latexdef "Funs" as "\mathrm{Funs}";
htmldef "Singleton" as "Singleton";
  althtmldef "Singleton" as "Singleton";
  latexdef "Singleton" as "\mathrm{Singleton}";
htmldef "Singletons" as "<IMG SRC='_singletons.gif' WIDTH=66 HEIGHT=19 " +
    "ALT=' Singletons' TITLE='Singletons'>";
  althtmldef "Singletons" as '<FONT FACE=sans-serif> Singletons </FONT>';
  latexdef "Singletons" as "\mathrm{Singletons}";
htmldef "Image" as "Image";
  althtmldef "Image" as "Image";
  latexdef "Image" as "\mathrm{Image}";
htmldef "Cart" as "Cart";
  althtmldef "Cart" as "Cart";
  latexdef "Cart" as "\mathrm{Cart}";
htmldef "Img" as "Img";
  althtmldef "Img" as "Img";
  latexdef "Img" as "\mathrm{Img}";
htmldef "Domain" as "Domain";
  althtmldef "Domain" as "Domain";
  latexdef "Domain" as "\mathrm{Domain}";
htmldef "Range" as "Range";
  althtmldef "Range" as "Range";
  latexdef "Range" as "\mathrm{Range}";
htmldef "pprod" as "pprod";
  althtmldef "pprod" as "pprod";
  latexdef "pprod" as "\mathrm{pprod}";
htmldef "Apply" as "Apply";
  althtmldef "Apply" as "Apply";
  latexdef "Apply" as "\mathrm{Apply}";
htmldef "Cup" as "Cup";
  althtmldef "Cup" as "Cup";
  latexdef "Cup" as "\mathrm{Cup}";
htmldef "Cap" as "Cap";
  althtmldef "Cap" as "Cap";
  latexdef "Cap" as "\mathrm{Cap}";
htmldef "Succ" as "Succ";
  althtmldef "Succ" as "Succ";
  latexdef "Succ" as "\mathrm{Succ}";
htmldef "Funpart" as "Funpart";
  althtmldef "Funpart" as "Funpart";
  latexdef "Funpart" as "\mathrm{Funpart}";
htmldef "FullFun" as "FullFun";
  althtmldef "FullFun" as "FullFun";
  latexdef "FullFun" as "\mathrm{FullFun}";
htmldef "Restrict" as "Restrict";
  althtmldef "Restrict" as "Restrict";
  latexdef "Restrict" as "\mathrm{Restrict}";
htmldef "LB" as "LB";
  althtmldef "LB" as "LB";
  latexdef "LB" as "\mathrm{LB}";
htmldef "UB" as "UB";
  althtmldef "UB" as "UB";
  latexdef "UB" as "\mathrm{UB}";
htmldef "<<" as
  "<IMG SRC='llangle.gif' WIDTH=6 HEIGHT=19 ALT=' &lt;&lt;' TITLE='&lt;&lt;'>";
  althtmldef "<<" as "&#10218;";
  latexdef "<<" as "\langle\langle";
htmldef ">>" as
  "<IMG SRC='rrangle.gif' WIDTH=6 HEIGHT=19 ALT=' &gt;&gt;' TITLE='&gt;&gt;'>";
  althtmldef ">>" as "&#10219;";
  latexdef ">>" as "\rangle\rangle";
htmldef "XX." as
    " <IMG SRC='_ttimes.gif' WIDTH=18 HEIGHT=19 ALT=' XX.' TITLE='XX.'> ";
  althtmldef "XX." as ' &times;&times; ';
  latexdef "XX." as "\times\times";
htmldef "EE" as "<IMG SRC='bbe.gif' WIDTH=11 HEIGHT=19 ALT=' EE' TITLE='EE'>";
  althtmldef "EE" as "&#x1D53C";
/*
htmldef "EE" as "<FONT FACE=sans-serif>&Eopf;</FONT>";
  althtmldef "EE" as "<FONT FACE=sans-serif>&#x1D53C</FONT>";
*/
  latexdef "EE" as "\mathbb{E}";
htmldef "Btwn" as
    " <IMG SRC='_btwn.gif' WIDTH=35 HEIGHT=19 ALT=' Btwn' TITLE='Btwn'> ";
  althtmldef "Btwn" as " Btwn ";
  latexdef "Btwn" as "\mathrm{Btwn}";
htmldef "Cgr" as "Cgr";
  althtmldef "Cgr" as "Cgr";
  latexdef "Cgr" as "\mathrm{Cgr}";
htmldef "OuterFiveSeg" as " <IMG SRC='_outerfiveseg.gif' WIDTH=89 HEIGHT=19 " +
    "ALT=' OuterFiveSeg' TITLE='OuterFiveSeg'> ";
  althtmldef "OuterFiveSeg" as " OuterFiveSeg ";
  latexdef "OuterFiveSeg" as "\mathrm{OuterFiveSeg}";
htmldef "TransportTo" as "TransportTo";
  althtmldef "TransportTo" as "TransportTo";
  latexdef "TransportTo" as "\mathbin{\operatorname{TransportTo}}";
htmldef "InnerFiveSeg" as " <IMG SRC='_innerfiveseg.gif' WIDTH=84 HEIGHT=19 " +
    "ALT=' InnerFiveSeg' TITLE='InnerFiveSeg'> ";
  althtmldef "InnerFiveSeg" as " InnerFiveSeg ";
  latexdef "InnerFiveSeg" as "\mathrm{InnerFiveSeg}";
htmldef "Cgr3" as "Cgr3";
  althtmldef "Cgr3" as "Cgr3";
  latexdef "Cgr3" as "\mathrm{Cgr3}";
htmldef "Colinear" as " <IMG SRC='_colinear.gif' WIDTH=54 HEIGHT=19 " +
    "ALT=' Colinear' TITLE='Colinear'> ";
  althtmldef "Colinear" as " Colinear ";
  latexdef "Colinear" as "\mathrm{Colinear}";
htmldef "FiveSeg" as " <IMG SRC='_fiveseg.gif' WIDTH=51 HEIGHT=19 " +
    "ALT=' FiveSeg' TITLE='FiveSeg'> ";
  althtmldef "FiveSeg" as " FiveSeg ";
  latexdef "FiveSeg" as "\mathrm{FiveSeg}";
/*
htmldef "==3" as
    " <IMG SRC='equiv.gif' WIDTH=12 HEIGHT=19 ALT=' ==' TITLE='=='>" +
    "<IMG SRC='sub3.gif' WIDTH=6 HEIGHT=19 ALT='3' TITLE='3'> ";
  althtmldef "==3" as " &#x2261;&#x2083; ";
  latexdef "==3" as "\equiv_3";
*/
htmldef "Seg<_" as " <IMG SRC='_segle.gif' WIDTH=30 HEIGHT=19 " +
    "ALT=' Seg&lt;_' TITLE='Seg&lt;_'> ";
  althtmldef "Seg<_" as " Seg<SUB>&le;</SUB> ";
  latexdef "Seg<_" as "\mathrm{Seg}_\le";
htmldef "OutsideOf" as "OutsideOf";
  althtmldef "OutsideOf" as "OutsideOf";
  latexdef "OutsideOf" as "\mathrm{OutsideOf}";
htmldef "Line" as "Line";
  althtmldef "Line" as "Line";
  latexdef "Line" as "\mathrm{Line}";
htmldef "LinesEE" as "LinesEE";
  althtmldef "LinesEE" as "LinesEE";
  latexdef "LinesEE" as "\mathrm{LinesEE}";
htmldef "Ray" as "Ray";
  althtmldef "Ray" as "Ray";
  latexdef "Ray" as "\mathrm{Ray}";
htmldef "BernPoly" as " BernPoly ";
  althtmldef "BernPoly" as " BernPoly ";
  latexdef "BernPoly" as "\mathrm{BernPoly}";

htmldef "Hf" as " Hf ";
  althtmldef "Hf" as " Hf ";
  latexdef "Hf" as "\mathrm{Hf}";

htmldef "prod_" as "<IMG SRC='prod.gif' WIDTH=12 HEIGHT=19 " +
    "ALT=' prod_' TITLE='prod_'>";
  althtmldef "prod_" as "&#x220F";
  latexdef "prod_" as "\prod";

htmldef "FallFac" as " FallFac ";
  althtmldef "FallFac" as " FallFac ";
  latexdef "FallFac" as "\mathrm{FallFac}";

htmldef "RiseFac" as " RiseFac ";
  althtmldef "RiseFac" as " RiseFac ";
  latexdef "RiseFac" as "\mathrm{RiseFac}";

htmldef "_/_\" as
    " <IMG SRC='bigtriangleup.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' _/_\' TITLE='_/_\'> ";
  althtmldef "_/_\" as " &#x25b3; ";
  latexdef "_/_\" as "\triangle";

htmldef "_/_\^n" as
    " <IMG SRC='bigtriangleup.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' _/_\^n' TITLE='_/_\^n'><SUP>n</SUP> ";
  althtmldef "_/_\^n" as " &#x25b3;<SUP>n</SUP> ";
  latexdef "_/_\^n" as "\triangle^\mathrm{n}";
/* End of Scott Fenton's mathbox */

/* Mathbox of Jeff Hankins */
/* End of Jeff Madsen's mathbox */

/* Mathbox of Anthony Hart */
/* End of Anthony Hart's mathbox */

/* Mathbox of Jeff Hoffman */
htmldef "gcdOLD" as
    "<IMG SRC='_gcd.gif' WIDTH=23 HEIGHT=19 ALT=' gcd' TITLE='gcd'>" +
    "<IMG SRC='_old.gif' WIDTH=23 HEIGHT=19 ALT='OLD' TITLE='OLD'>";
  althtmldef "gcdOLD" as " gcd<SUB>OLD</SUB> ";
  latexdef "gcdOLD" as "\operatorname{gcd_{OLD}}";
/* End of Jeff Hoffman's mathbox */

/* Mathbox of Matthew House */
htmldef "TC+" as
    "<IMG SRC='_tc.gif' WIDTH=20 HEIGHT=19 ALT=' TC' TITLE='TC'>" +
    "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT='+' TITLE='+'> ";
  althtmldef "TC+" as 'TC+ ';
  latexdef "TC+" as "\operatorname{TC+}";
/* End of Matthew House's mathbox */

/* Mathbox of Jeff Madsen */
htmldef "Fne" as
    "<IMG SRC='_fne.gif' WIDTH=24 HEIGHT=19 ALT=' Fne' TITLE='Fne'>";
  althtmldef "Fne" as "Fne";
  latexdef "Fne" as "\mathrm{Fne}";
htmldef "Ref" as
    "<IMG SRC='_ref.gif' WIDTH=23 HEIGHT=19 ALT=' Ref' TITLE='Ref'>";
  althtmldef "Ref" as "Ref";
  latexdef "Ref" as "\mathrm{Ref}";
htmldef "PtFin" as
    "<IMG SRC='_ptfin.gif' WIDTH=36 HEIGHT=19 ALT=' PtFin' TITLE='PtFin'>";
  althtmldef "PtFin" as "PtFin";
  latexdef "PtFin" as "\mathrm{PtFin}";
htmldef "LocFin" as
    "<IMG SRC='_locfin.gif' WIDTH=44 HEIGHT=19 ALT=' LocFin' TITLE='LocFin'>";
  althtmldef "LocFin" as "LocFin";
  latexdef "LocFin" as "\mathrm{LocFin}";
htmldef "TotBnd" as
    "<IMG SRC='_totbnd.gif' WIDTH=46 HEIGHT=19 ALT=' TotBnd' TITLE='TotBnd'>";
  althtmldef "TotBnd" as "TotBnd";
  latexdef "TotBnd" as "\mathrm{TotBnd}";
htmldef "Bnd" as
    "<IMG SRC='_bnd.gif' WIDTH=25 HEIGHT=19 ALT=' Bnd' TITLE='Bnd'>";
  althtmldef "Bnd" as "Bnd";
  latexdef "Bnd" as "\mathrm{Bnd}";
htmldef "Ismty" as
    " <IMG SRC='_ismty.gif' WIDTH=36 HEIGHT=19 ALT=' Ismty' TITLE='Ismty'> ";
  althtmldef "Ismty" as " Ismty ";
  latexdef "Ismty" as "\mathrm{Ismty}";
htmldef "Rn" as
    "<IMG SRC='_bbrn.gif' WIDTH=19 HEIGHT=19 ALT=' Rn' TITLE='Rn'>";
  althtmldef "Rn" as "&#8477;<I><SUP>n</SUP></I>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "Rn" as "\mathbb{R}^n";
htmldef "RingOpsHom" as
   " <IMG SRC='_rnghom.gif' WIDTH=55 HEIGHT=19" +
   " ALT=' RingOpsHom' TITLE='RingOpsHom'> ";
  althtmldef "RingOpsHom" as " RingOpsHom ";
  latexdef "RingOpsHom" as "\mathrm{RingOpsHom}";
htmldef "RingOpsIso" as
   " <IMG SRC='_rngiso.gif' WIDTH=43 HEIGHT=19" +
   " ALT=' RingOpsIso' TITLE='RingOpsIso'> ";
  althtmldef "RingOpsIso" as " RingOpsIso ";
  latexdef "RingOpsIso" as "\mathrm{RingOpsIso}";
htmldef "~=R" as
    " <IMG SRC='_simeqr.gif' WIDTH=18 HEIGHT=19 ALT=' ~=R' TITLE='~=R'> ";
  althtmldef "~=R" as " &#8771;<SUB>&#x1D45F;</SUB> ";
  latexdef "~=R" as "\simeq_r";
htmldef "CRingOps" as "CRingOps";
  althtmldef "CRingOps" as "CRingOps";
  latexdef "CRingOps" as "\mathrm{CRingOps}";
htmldef "Idl" as
    "<IMG SRC='_idl.gif' WIDTH=16 HEIGHT=19 ALT=' Idl' TITLE='Idl'>";
  althtmldef "Idl" as "Idl";
  latexdef "Idl" as "\mathrm{Idl}";
htmldef "PrIdl" as
    "<IMG SRC='_pridl.gif' WIDTH=31 HEIGHT=19 ALT=' PrIdl' TITLE='PrIdl'>";
  althtmldef "PrIdl" as "PrIdl";
  latexdef "PrIdl" as "\mathrm{PrIdl}";
htmldef "MaxIdl" as
    "<IMG SRC='_maxidl.gif' WIDTH=44 HEIGHT=19 ALT=' MaxIdl' TITLE='MaxIdl'>";
  althtmldef "MaxIdl" as "MaxIdl";
  latexdef "MaxIdl" as "\mathrm{MaxIdl}";
htmldef "PrRing" as
    "<IMG SRC='_prring.gif' WIDTH=45 HEIGHT=19 ALT=' PrRing' TITLE='PrRing'>";
  althtmldef "PrRing" as "PrRing";
  latexdef "PrRing" as "\mathrm{PrRing}";
htmldef "Dmn" as
    "<IMG SRC='_dmn.gif' WIDTH=30 HEIGHT=19 ALT=' Dmn' TITLE='Dmn'>";
  althtmldef "Dmn" as "Dmn";
  latexdef "Dmn" as "\mathrm{Dmn}";
htmldef "IdlGen" as
   " <IMG SRC='_idlgen.gif' WIDTH=42 HEIGHT=19 ALT=' IdlGen' TITLE='IdlGen'> ";
  althtmldef "IdlGen" as " IdlGen ";
  latexdef "IdlGen" as "\mathrm{IdlGen}";
/* End of Jeff Madsen's mathbox */

/* Mathbox of Peter Mazsa */
htmldef "|X." as
    " <IMG SRC='ltimes.gif' WIDTH=10 HEIGHT=19 ALT=' |X.' TITLE='|X.'> ";
  althtmldef "|X." as " &#x22C9; ";
  latexdef "|X." as "\ltimes";
htmldef "QMap" as ' QMap ';
  althtmldef "QMap" as ' QMap ';
  latexdef "QMap" as "\mathrm{QMap}";
htmldef "AdjLiftMap" as ' AdjLiftMap ';
  althtmldef "AdjLiftMap" as ' AdjLiftMap ';
  latexdef "AdjLiftMap" as "\mathrm{AdjLiftMap}";
htmldef "BlockLiftMap" as ' BlockLiftMap ';
  althtmldef "BlockLiftMap" as ' BlockLiftMap ';
  latexdef "BlockLiftMap" as "\mathrm{BlockLiftMap}";
htmldef "SucMap" as ' SucMap ';
  althtmldef "SucMap" as ' SucMap ';
  latexdef "SucMap" as "\mathrm{SucMap}";
htmldef "Suc" as ' Suc ';
  althtmldef "Suc" as ' Suc ';
  latexdef "Suc" as "\mathrm{Suc}";
htmldef "pre" as ' pre ';
  althtmldef "pre" as ' pre ';
  latexdef "pre" as "\mathrm{pre}";
htmldef "BlockLiftFix" as ' BlockLiftFix ';
  althtmldef "BlockLiftFix" as ' BlockLiftFix ';
  latexdef "BlockLiftFix" as "\mathrm{BlockLiftFix}";
htmldef "ShiftStable" as ' ShiftStable ';
  althtmldef "ShiftStable" as ' ShiftStable ';
  latexdef "ShiftStable" as "\mathrm{ShiftStable}";
htmldef ",~" as
    " <IMG SRC='wr.gif' WIDTH=5 HEIGHT=19 ALT=' ,~' TITLE=',~'> ";
  althtmldef ",~" as ' &#8768; ';
  latexdef ",~" as "\wr";
htmldef "~" as
    " <IMG SRC='sim.gif' WIDTH=13 HEIGHT=19 ALT=' ~' TITLE='~'> ";
  althtmldef "~" as ' &#8764; ';
  latexdef "~" as "\sim";
htmldef "Rels" as ' Rels ';
  althtmldef "Rels" as ' Rels ';
  latexdef "Rels" as "\mathrm{Rels}";
htmldef "_S" as
    " <IMG SRC='rmcs.gif' WIDTH=4 HEIGHT=19 ALT=' _S' TITLE='_S'> ";
  althtmldef "_S" as ' S ';
  latexdef "_S" as "\mathrm{S}";
htmldef "Refs" as ' Refs ';
  althtmldef "Refs" as ' Refs ';
  latexdef "Refs" as "\mathrm{Refs}";
htmldef "RefRels" as ' RefRels ';
  althtmldef "RefRels" as ' RefRels ';
  latexdef "RefRels" as "\mathrm{RefRels}";
htmldef "RefRel" as ' RefRel ';
  althtmldef "RefRel" as ' RefRel ';
  latexdef "RefRel" as "\mathrm{RefRel}";
htmldef "CnvRefs" as ' CnvRefs ';
  althtmldef "CnvRefs" as ' CnvRefs ';
  latexdef "CnvRefs" as "\mathrm{CnvRefs}";
htmldef "CnvRefRels" as ' CnvRefRels ';
  althtmldef "CnvRefRels" as ' CnvRefRels ';
  latexdef "CnvRefRels" as "\mathrm{CnvRefRels}";
htmldef "CnvRefRel" as ' CnvRefRel ';
  althtmldef "CnvRefRel" as ' CnvRefRel ';
  latexdef "CnvRefRel" as "\mathrm{CnvRefRel}";
htmldef "Syms" as ' Syms ';
  althtmldef "Syms" as ' Syms ';
  latexdef "Syms" as "\mathrm{Syms}";
htmldef "SymRels" as ' SymRels ';
  althtmldef "SymRels" as ' SymRels ';
  latexdef "SymRels" as "\mathrm{SymRels}";
htmldef "SymRel" as ' SymRel ';
  althtmldef "SymRel" as ' SymRel ';
  latexdef "SymRel" as "\mathrm{SymRel}";
htmldef "Trs" as ' Trs ';
  althtmldef "Trs" as ' Trs ';
  latexdef "Trs" as "\mathrm{Trs}";
htmldef "TrRels" as ' TrRels ';
  althtmldef "TrRels" as ' TrRels ';
  latexdef "TrRels" as "\mathrm{TrRels}";
htmldef "TrRel" as ' TrRel ';
  althtmldef "TrRel" as ' TrRel ';
  latexdef "TrRel" as "\mathrm{TrRel}";
htmldef "EqvRels" as ' EqvRels ';
  althtmldef "EqvRels" as ' EqvRels ';
  latexdef "EqvRels" as "\mathrm{EqvRels}";
htmldef "EqvRel" as ' EqvRel ';
  althtmldef "EqvRel" as ' EqvRel ';
  latexdef "EqvRel" as "\mathrm{EqvRel}";
htmldef "CoElEqvRels" as ' CoElEqvRels ';
  althtmldef "CoElEqvRels" as ' CoElEqvRels ';
  latexdef "CoElEqvRels" as "\mathrm{CoElEqvRels}";
htmldef "CoElEqvRel" as ' CoElEqvRel ';
  althtmldef "CoElEqvRel" as ' CoElEqvRel ';
  latexdef "CoElEqvRel" as "\mathrm{CoElEqvRel}";
htmldef "Redunds" as ' Redunds ';
  althtmldef "Redunds" as ' Redunds ';
  latexdef "Redunds" as "\mathrm{Redunds}";
htmldef "Redund" as ' Redund ';
  althtmldef "Redund" as ' Redund ';
  latexdef "Redund" as "\mathrm{Redund}";
htmldef "redund" as ' redund ';
  althtmldef "redund" as ' redund ';
  latexdef "redund" as "\mathrm{redund}";
htmldef "DomainQss" as ' DomainQss ';
  althtmldef "DomainQss" as ' DomainQss ';
  latexdef "DomainQss" as "\mathrm{DomainQss}";
htmldef "DomainQs" as ' DomainQs ';
  althtmldef "DomainQs" as ' DomainQs ';
  latexdef "DomainQs" as "\mathrm{DomainQs}";
htmldef "Ers" as ' Ers ';
  althtmldef "Ers" as ' Ers ';
  latexdef "Ers" as "\mathrm{Ers}";
htmldef "ErALTV" as ' ErALTV ';
  althtmldef "ErALTV" as ' ErALTV ';
  latexdef "ErALTV" as "\mathrm{ErALTV}";
htmldef "PetErs" as ' PetErs ';
  althtmldef "PetErs" as ' PetErs ';
  latexdef "PetErs" as "\mathrm{PetErs}";
htmldef "Pet2Ers" as ' Pet2Ers ';
  althtmldef "Pet2Ers" as ' Pet2Ers ';
  latexdef "Pet2Ers" as "\mathrm{Pet2Ers}";
htmldef "CoMembErs" as ' CoMembErs ';
  althtmldef "CoMembErs" as ' CoMembErs ';
  latexdef "CoMembErs" as "\mathrm{CoMembErs}";
htmldef "CoMembEr" as ' CoMembEr ';
  althtmldef "CoMembEr" as ' CoMembEr ';
  latexdef "CoMembEr" as "\mathrm{CoMembEr}";
htmldef "Funss" as ' Funss ';
  althtmldef "Funss" as ' Funss ';
  latexdef "Funss" as "\mathrm{Funss}";
htmldef "FunsALTV" as ' FunsALTV ';
  althtmldef "FunsALTV" as ' FunsALTV ';
  latexdef "FunsALTV" as "\mathrm{FunsALTV}";
htmldef "FunALTV" as ' FunALTV ';
  althtmldef "FunALTV" as ' FunALTV ';
  latexdef "FunALTV" as "\mathrm{FunALTV}";
htmldef "Disjss" as ' Disjss ';
  althtmldef "Disjss" as ' Disjss ';
  latexdef "Disjss" as "\mathrm{Disjss}";
htmldef "Disjs" as ' Disjs ';
  althtmldef "Disjs" as ' Disjs ';
  latexdef "Disjs" as "\mathrm{Disjs}";
htmldef "Disj" as ' Disj ';
  althtmldef "Disj" as ' Disj ';
  latexdef "Disj" as "\mathrm{Disj}";
htmldef "ElDisjs" as ' ElDisjs ';
  althtmldef "ElDisjs" as ' ElDisjs ';
  latexdef "ElDisjs" as "\mathrm{ElDisjs}";
htmldef "ElDisj" as ' ElDisj ';
  althtmldef "ElDisj" as ' ElDisj ';
  latexdef "ElDisj" as "\mathrm{ElDisj}";
htmldef "AntisymRel" as ' AntisymRel ';
  althtmldef "AntisymRel" as ' AntisymRel ';
  latexdef "AntisymRel" as "\mathrm{AntisymRel}";
htmldef "Parts" as ' Parts ';
  althtmldef "Parts" as ' Parts ';
  latexdef "Parts" as "{\rm Parts}";
htmldef "Part" as ' Part ';
  althtmldef "Part" as ' Part ';
  latexdef "Part" as "{\rm Part}";
htmldef "MembParts" as ' MembParts ';
  althtmldef "MembParts" as ' MembParts ';
  latexdef "MembParts" as "{\rm MembParts}";
htmldef "MembPart" as ' MembPart ';
  althtmldef "MembPart" as ' MembPart ';
  latexdef "MembPart" as "{\rm MembPart}";
htmldef "PetParts" as ' PetParts ';
  althtmldef "PetParts" as ' PetParts ';
  latexdef "PetParts" as "\mathrm{PetParts}";
htmldef "Pet2Parts" as ' Pet2Parts ';
  althtmldef "Pet2Parts" as ' Pet2Parts ';
  latexdef "Pet2Parts" as "\mathrm{Pet2Parts}";
/* End of Peter Mazsa's mathbox */

/* Mathbox of Rodolfo Medina */
htmldef "Prt" as
    "<IMG SRC='_prt.gif' WIDTH=21 HEIGHT=19 ALT=' Prt' TITLE='Prt'> ";
  althtmldef "Prt" as "Prt ";
  latexdef "Prt" as "\mathrm{Prt}";
/* End of Rodolfo Medina's mathbox */

/* Mathbox of metakunt */
htmldef "CSRing" as ' CSRing ';
  althtmldef "CSRing" as ' CSRing ';
  latexdef "CSRing" as "\mathrm{CSRing}";
htmldef "PrimRoots" as ' PrimRoots ';
  althtmldef "PrimRoots" as ' PrimRoots ';
  latexdef "PrimRoots" as "\mathrm{PrimRoots}";
/* End of metakunt's mathbox */

/* Mathbox of Steven Nguyen */
htmldef "-R" as
    " <IMG SRC='minus.gif' WIDTH=11 HEIGHT=19 ALT=' -' TITLE='-'><SUB>" +
    "<IMG SRC='bbr.gif' WIDTH=9 HEIGHT=14 ALT='RR' TITLE='RR'></SUB>&#x200A;";
  althtmldef "-R" as " &minus;<SUB>&#8477;</SUB> ";
  latexdef "-R" as " -_\mathbb{R} ";
htmldef "/R" as
    " <IMG SRC='solidus.gif' WIDTH=6 HEIGHT=19 ALT=' /' TITLE='/'>" +
    "<IMG SRC='bbr.gif' WIDTH=9 HEIGHT=14 ALT='RR' TITLE='RR'></SUB>&#x200A;";
  althtmldef "/R" as " /<SUB>&#8477;</SUB> ";
  latexdef "/R" as " /_\mathbb{R} ";
htmldef "PrjSp" as
    "<IMG SRC='bbp.gif' WIDTH=11 HEIGHT=19 ALT=' P' TITLE='P'>roj";
  althtmldef "PrjSp" as "&#8473;&#x1D563;&#x1D560;&#x1D55B;";
  latexdef "PrjSp" as "\operatorname{\mathbb{Proj}}";
htmldef "PrjSpn" as
    "<IMG SRC='bbp.gif' WIDTH=11 HEIGHT=19 ALT=' P' TITLE='P'>roj" +
    "<SUB>n</SUB>";
  althtmldef "PrjSpn" as "&#8473;&#x1D563;&#x1D560;&#x1D55B;<SUB>n</SUB>";
  latexdef "PrjSpn" as "\operatorname{\mathbb{Proj}_\mathrm{n}}";
htmldef "PrjCrv" as
    "<IMG SRC='bbp.gif' WIDTH=11 HEIGHT=19 ALT=' P' TITLE='P'>rojCrv";
  althtmldef "PrjCrv" as "&#8473;&#x1D563;&#x1D560;&#x1D55B;Crv";
  latexdef "PrjCrv" as "\operatorname{\mathbb{Proj}Crv}";
/* End of Steven Nguyen's mathbox */

/* Mathbox of Stefan O'Rear */
htmldef "NoeACS" as "NoeACS";
  althtmldef "NoeACS" as "NoeACS";
  latexdef "NoeACS" as "\mathrm{NoeACS}";
htmldef "mzPolyCld" as "mzPolyCld";
  althtmldef "mzPolyCld" as "mzPolyCld";
  latexdef "mzPolyCld" as "\mathrm{mzPolyCld}";
htmldef "mzPoly" as "mzPoly";
  althtmldef "mzPoly" as "mzPoly";
  latexdef "mzPoly" as "\mathrm{mzPoly}";
htmldef "Dioph" as "Dioph";
  althtmldef "Dioph" as "Dioph";
  latexdef "Dioph" as "\mathrm{Dioph}";
htmldef "numer" as "numer";
  althtmldef "numer" as "numer";
  latexdef "numer" as "\mathrm{numer}";
htmldef "denom" as "denom";
  althtmldef "denom" as "denom";
  latexdef "denom" as "\mathrm{denom}";
htmldef "Pell1QR" as "Pell1QR";
  althtmldef "Pell1QR" as "Pell1QR";
  latexdef "Pell1QR" as "\mathrm{Pell1QR}";
htmldef "Pell14QR" as "Pell14QR";
  althtmldef "Pell14QR" as "Pell14QR";
  latexdef "Pell14QR" as "\mathrm{Pell14QR}";
htmldef "Pell1234QR" as "Pell1234QR";
  althtmldef "Pell1234QR" as "Pell1234QR";
  latexdef "Pell1234QR" as "\mathrm{Pell1234QR}";
htmldef "PellFund" as "PellFund";
  althtmldef "PellFund" as "PellFund";
  latexdef "PellFund" as "\mathrm{PellFund}";
htmldef "[]NN" as "&#x25FB;<SUB><I>NN</I></SUB>";
  althtmldef "[]NN" as "&#x25FB;<SUB><I>NN</I></SUB>";
  latexdef "[]NN" as "\mathrm{[]NN}";
htmldef "rmX" as " X<SUB>rm</SUB> ";
  althtmldef "rmX" as " X<SUB>rm</SUB> ";
  latexdef "rmX" as "\mathrm{rmX}";
htmldef "rmY" as " Y<SUB>rm</SUB> ";
  althtmldef "rmY" as " Y<SUB>rm</SUB> ";
  latexdef "rmY" as "\mathrm{rmY}";
htmldef "LFinGen" as "LFinGen";
  althtmldef "LFinGen" as "LFinGen";
  latexdef "LFinGen" as "\mathrm{LFinGen}";
htmldef "LNoeM" as "LNoeM";
  althtmldef "LNoeM" as "LNoeM";
  latexdef "LNoeM" as "\mathrm{LNoeM}";
htmldef "LIndF" as " LIndF ";
  althtmldef "LIndF" as " LIndF ";
  latexdef "LIndF" as " \mathrm{LIndF} ";
htmldef "LIndS" as "LIndS";
  althtmldef "LIndS" as "LIndS";
  latexdef "LIndS" as "\mathrm{LIndS}";
htmldef "LNoeR" as "LNoeR";
  althtmldef "LNoeR" as "LNoeR";
  latexdef "LNoeR" as "\mathrm{LNoeR}";
htmldef "ldgIdlSeq" as "ldgIdlSeq";
  althtmldef "ldgIdlSeq" as "ldgIdlSeq";
  latexdef "ldgIdlSeq" as "\mathrm{ldgIdlSeq}";
htmldef "Monic" as
    " <IMG SRC='_monic.gif' WIDTH=38 HEIGHT=19 ALT=' Monic' TITLE='Monic'> ";
  althtmldef "Monic" as " Monic ";
  latexdef "Monic" as "\mathrm{Monic}";
htmldef "Poly<" as " Poly<sub>&lt;</sub> ";
  althtmldef "Poly<" as " Poly<sub>&lt;</sub> ";
  latexdef "Poly<" as "\mathrm{Poly<}";
htmldef "degAA" as "deg<SUB>AA</SUB>";
  althtmldef "degAA" as "deg<SUB>AA</SUB>";
  latexdef "degAA" as "\mathrm{degAA}";
htmldef "minPolyAA" as "minPolyAA";
  althtmldef "minPolyAA" as "minPolyAA";
  latexdef "minPolyAA" as "\mathrm{minPolyAA}";
htmldef "_ZZ" as "<SPAN STYLE='text-decoration: overline;'>&#8484;</SPAN>";
    /* 2-Jan-2016 reverted sans-serif */
  althtmldef "_ZZ" as
                 "<SPAN STYLE='text-decoration: overline;'>&#8484;</SPAN>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "_ZZ" as "\mathrm{_ZZ}";
htmldef "IntgOver" as "IntgOver";
  althtmldef "IntgOver" as "IntgOver";
  latexdef "IntgOver" as "\mathrm{IntgOver}";
htmldef "MEndo" as "MEndo";
  althtmldef "MEndo" as "MEndo";
  latexdef "MEndo" as "\mathrm{MEndo}";
htmldef "SubDRing" as "SubDRing";
  althtmldef "SubDRing" as "SubDRing";
  latexdef "SubDRing" as "\mathrm{SubDRing}";
htmldef "Cntr" as "Cntr";
  althtmldef "Cntr" as "Cntr";
  latexdef "Cntr" as "\mathrm{Cntr}";
htmldef "Cntz" as "Cntz";
  althtmldef "Cntz" as "Cntz";
  latexdef "Cntz" as "\mathrm{Cntz}";
htmldef "CytP" as "CytP";
  althtmldef "CytP" as "CytP";
  latexdef "CytP" as "\mathrm{CytP}";
htmldef "TopSep" as "TopSep";
  althtmldef "TopSep" as "TopSep";
  latexdef "TopSep" as "\mathrm{TopSep}";
htmldef "TopLnd" as "TopLnd";
  althtmldef "TopLnd" as "TopLnd";
  latexdef "TopLnd" as "\mathrm{TopLnd}";
/* End of Stefan O'Rear's mathbox */

/* Mathbox of Rohan Ridenour */
htmldef "Coll" as " Coll ";
  althtmldef "Coll" as " Coll ";
  latexdef "Coll" as "\mathrm{Coll}";
htmldef "SimpGrp" as "SimpGrp";
  althtmldef "SimpGrp" as "SimpGrp";
  latexdef "SimpGrp" as "\mathrm{SimpGrp}";
htmldef "MndRing" as " MndRing ";
  althtmldef "MndRing" as " MndRing ";
  latexdef "MndRing" as "\mathrm{MndRing}";
/* End of Rohan Ridenour's mathbox */

/* Mathbox of Steve Rodriguez */
htmldef "_Cc" as "C<SUB>&#x1D450;</SUB>";
  althtmldef "_Cc" as "C<SUB>&#x1D450;</SUB>";
  latexdef "_Cc" as "\mathrm{C}_c";
/* End of Steve Rodriguez's mathbox */

/* Mathbox of Andrew Salmon */
/* geometry proposal */
htmldef "+r" as "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>" +
    "<IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 ALT='r' TITLE='r'>";
  althtmldef "+r" as "+<SUB>&#x1D45F;</SUB>";
  latexdef "+r" as "+_r";
htmldef "-r" as
    "<IMG SRC='minus.gif' WIDTH=11 HEIGHT=19 ALT=' -' TITLE='-'>" +
    "<IMG SRC='subr.gif' WIDTH=5 HEIGHT=19 ALT='r' TITLE='r'>";
  althtmldef "-r" as "-<SUB>&#x1D45F;</SUB>";
  latexdef "-r" as "-_r";
htmldef ".v" as "<IMG SRC='cdot.gif' WIDTH=4 HEIGHT=19 ALT=' .' TITLE='.'>" +
    "<IMG SRC='subv.gif' WIDTH=6 HEIGHT=19 ALT='v' TITLE='v'>";
  althtmldef ".v" as ".<SUB>&#x1D463;</SUB>";
  latexdef ".v" as "._v";
htmldef "PtDf" as
    "<IMG SRC='_ptdf.gif' WIDTH=31 HEIGHT=19 ALT=' PtDf' TITLE='PtDf'>";
  althtmldef "PtDf" as "PtDf";
  latexdef "PtDf" as "\mathrm{PtDf}";
htmldef "RR3" as
    "<IMG SRC='bbr.gif' WIDTH=13 HEIGHT=19 ALT=' RR' TITLE='RR'>" +
    "<IMG SRC='sup3.gif' WIDTH=6 HEIGHT=19 ALT='3' TITLE='3'>";
  althtmldef "RR3" as "RR3";
  latexdef "RR3" as "\mathrm{RR3}";
/*
htmldef "plane3" as
    "<IMG SRC='_plane.gif' WIDTH=35 HEIGHT=19 ALT=' plane' TITLE='plane'>" +
    "<IMG SRC='sup3.gif' WIDTH=6 HEIGHT=19 ALT='3' TITLE='3'>";
  althtmldef "plane3" as "plane3";
  latexdef "plane3" as "\mathrm{plane3}";
*/
htmldef "line3" as
    "<IMG SRC='_line.gif' WIDTH=23 HEIGHT=19 ALT=' line' TITLE='line'>" +
    "<IMG SRC='sup3.gif' WIDTH=6 HEIGHT=19 ALT='3' TITLE='3'>";
  althtmldef "line3" as "line3";
  latexdef "line3" as "\mathrm{line3}";
/* End of Andrew Salmon's mathbox */

/* Mathbox of Jarvin Udandy */
htmldef "jph" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jph</I></SPAN>';
  althtmldef "jph" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jph</I></SPAN>';
  latexdef "jph" as "\mathrm{jph}";
htmldef "jps" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jps</I></SPAN>';
  althtmldef "jps" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jps</I></SPAN>';
  latexdef "jps" as "\mathrm{jps}";
htmldef "jch" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jch</I></SPAN>';
  althtmldef "jch" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jch</I></SPAN>';
  latexdef "jch" as "\mathrm{jch}";
htmldef "jth" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jth</I></SPAN>';
  althtmldef "jth" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jth</I></SPAN>';
  latexdef "jth" as "\mathrm{jth}";
htmldef "jta" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jta</I></SPAN>';
  althtmldef "jta" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jta</I></SPAN>';
  latexdef "jta" as "\mathrm{jta}";
htmldef "jet" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jet</I></SPAN>';
  althtmldef "jet" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jet</I></SPAN>';
  latexdef "jet" as "\mathrm{jet}";
htmldef "jze" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jze</I></SPAN>';
  althtmldef "jze" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jze</I></SPAN>';
  latexdef "jze" as "\mathrm{jze}";
htmldef "jsi" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jps</I></SPAN>';
  althtmldef "jsi" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jps</I></SPAN>';
  latexdef "jsi" as "\mathrm{jsi}";
htmldef "jrh" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jrh</I></SPAN>';
  althtmldef "jrh" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jrh</I></SPAN>';
  latexdef "jrh" as "\mathrm{jrh}";
htmldef "jmu" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jmu</I></SPAN>';
  althtmldef "jmu" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jmu</I></SPAN>';
  latexdef "jmu" as "\mathrm{jmu}";
htmldef "jla" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jla</I></SPAN>';
  althtmldef "jla" as
    '<SPAN CLASS=wff STYLE="color:blue"><I>jla</I></SPAN>';
  latexdef "jla" as "\mathrm{jla}";
/* End of Jarvin Udandy's mathbox */

/* Mathbox of Alexander van der Vekens */
htmldef "iota'" as 'iota&#39';
 althtmldef "iota'" as '&#8489;&#39';
 latexdef "iota'" as "\text\riota'";
htmldef "defAt" as ' defAt ';
 althtmldef "defAt" as ' defAt ';
 latexdef "defAt" as "\mathrm{defAt}";
htmldef "'''" as '&#39&#39&#39';
 althtmldef "'''" as '&#39&#39&#39';
 latexdef "'''" as "'''";
htmldef "''''" as '&#39&#39&#39&#39';
 althtmldef "''''" as '&#39&#39&#39&#39';
 latexdef "''''" as "''''";
htmldef "((" as ' ((';
 althtmldef "((" as ' ((';
 latexdef "((" as " ((";
htmldef "))" as ')) ';
 althtmldef "))" as ')) ';
 latexdef "))" as ")) ";
htmldef "e//" as
    " _<IMG SRC='notin.gif' WIDTH=10 HEIGHT=19 ALT=' e//' TITLE='e//'> ";
  althtmldef "e//" as ' _&notin; ';
 latexdef "e//" as "\notin";
htmldef "RePart" as 'RePart';
 althtmldef "RePart" as 'RePart';
 latexdef "RePart" as "\mathrm{RePart}";
htmldef "FermatNo" as 'FermatNo';
 althtmldef "FermatNo" as 'FermatNo';
 latexdef "FermatNo" as "\mathrm{FermatNo}";
htmldef "Even" as ' Even ';
 althtmldef "Even" as ' Even ';
 latexdef "Even" as "\mathrm{Even}";
htmldef "Odd" as ' Odd ';
 althtmldef "Odd" as ' Odd ';
 latexdef "Odd" as "\mathrm{Odd}";
htmldef "FPPr" as ' FPPr ';
 althtmldef "FPPr" as ' FPPr ';
 latexdef "FPPr" as "\mathrm{FPPr}";
htmldef "GoldbachEven" as ' GoldbachEven ';
 althtmldef "GoldbachEven" as ' GoldbachEven ';
 latexdef "GoldbachEven" as "\mathrm{GoldbachEven}";
htmldef "GoldbachOddW" as ' GoldbachOddW ';
 althtmldef "GoldbachOddW" as ' GoldbachOddW ';
 latexdef "GoldbachOddW" as "\mathrm{GoldbachOddW}";
htmldef "GoldbachOdd" as ' GoldbachOdd ';
 althtmldef "GoldbachOdd" as ' GoldbachOdd ';
 latexdef "GoldbachOdd" as "\mathrm{GoldbachOdd}";
htmldef "prefix" as ' prefix ';
 althtmldef "prefix" as ' prefix ';
 latexdef "prefix" as "\mathbin{\operatorname{prefix}}";
/* Graph theory (extension) */
htmldef "ClNeighbVtx" as ' ClNeighbVtx ';
  althtmldef "ClNeighbVtx" as ' ClNeighbVtx ';
  latexdef "ClNeighbVtx" as "\mathrm{ClNeighbVtx}";
htmldef "ISubGr" as " ISubGr ";
 althtmldef "ISubGr" as " ISubGr ";
 latexdef "ISubGr" as "\mathrm{ISubGr}";
htmldef "GraphIsom" as " GraphIsom ";
 althtmldef "GraphIsom" as " GraphIsom ";
 latexdef "GraphIsom" as "\mathrm{GraphIsom}";
htmldef "GraphIso" as " GraphIso ";
 althtmldef "GraphIso" as " GraphIso ";
 latexdef "GraphIso" as "\mathrm{GraphIso}";
htmldef "~=gr" as " <IMG SRC='simeq.gif' WIDTH=26 HEIGHT=19 " +
    "ALT=' ~=gr' TITLE='~=gr'><SUB>&#x1D454;&#x1D45F;</SUB> ";
  althtmldef "~=gr" as " &#8771;<SUB>&#x1D454;&#x1D45F;</SUB> ";
  latexdef "~=gr" as "\simeq_{gr}";
htmldef "GrTriangles" as "GrTriangles";
 althtmldef "GrTriangles" as "GrTriangles";
 latexdef "GrTriangles" as "\mathrm{GrTriangles}";
htmldef "StarGr" as "StarGr";
 althtmldef "StarGr" as "StarGr";
 latexdef "StarGr" as "\mathrm{StarGr}";
htmldef "GraphLocIso" as " GraphLocIso ";
 althtmldef "GraphLocIso" as " GraphLocIso ";
 latexdef "GraphLocIso" as "\mathrm{GraphLocIso}";
htmldef "~=lgr" as " <IMG SRC='simeq.gif' WIDTH=26 HEIGHT=19 " +
    "ALT=' ~=lgr' TITLE='~=lgr'><SUB>&#x1D459;&#x1D454;&#x1D45F;</SUB> ";
  althtmldef "~=lgr" as " &#8771;<SUB>&#x1D459;&#x1D454;&#x1D45F;</SUB> ";
  latexdef "~=lgr" as "\simeq_{lgr}";
htmldef "gPetersenGr" as " gPetersenGr ";
 althtmldef "gPetersenGr" as " gPetersenGr ";
 latexdef "gPetersenGr" as "\mathrm{gPetersenGr}";
htmldef "UPWalks" as "UPWalks";
 althtmldef "UPWalks" as "UPWalks";
 latexdef "UPWalks" as "\mathrm{UPWalks}";
/* Set of unordered pairs */
htmldef "<>" as '<>';
  althtmldef "<>" as "&#8644;";
  latexdef "<>" as "<>";
htmldef "Pairs" as 'Pairs';
 althtmldef "Pairs" as 'Pairs';
 latexdef "Pairs" as "\mathrm{Pairs}";
htmldef "PrPairs" as 'PrPairs';
 althtmldef "PrPairs" as 'Pairs<sub>proper</sub>';
 latexdef "PrPairs" as "\mathrm{Pairs}_proper";
/* Monoids (extension)  */
htmldef "MgmHom" as ' MgmHom ';
 althtmldef "MgmHom" as ' MgmHom ';
 latexdef "MgmHom" as "\mathrm{MgmHom}";
htmldef "SubMgm" as 'SubMgm';
 althtmldef "SubMgm" as 'SubMgm';
 latexdef "SubMgm" as "\mathrm{SubMgm}";
htmldef "EndoFMnd" as 'EndoFMnd';
 althtmldef "EndoFMnd" as 'EndoFMnd';
 latexdef "EndoFMnd" as "\mathrm{EndoFMnd}";
htmldef "clLaw" as ' clLaw ';
 althtmldef "clLaw" as ' clLaw ';
 latexdef "clLaw" as "\mathrm{clLaw}";
htmldef "assLaw" as ' assLaw ';
 althtmldef "assLaw" as ' assLaw ';
 latexdef "assLaw" as "\mathrm{assLaw}";
htmldef "comLaw" as ' comLaw ';
 althtmldef "comLaw" as ' comLaw ';
 latexdef "comLaw" as "\mathrm{comLaw}";
htmldef "intOp" as ' intOp ';
 althtmldef "intOp" as ' intOp ';
 latexdef "intOp" as "\mathrm{intOp}";
htmldef "clIntOp" as ' clIntOp ';
 althtmldef "clIntOp" as ' clIntOp ';
 latexdef "clIntOp" as "\mathrm{clIntOp}";
htmldef "assIntOp" as ' assIntOp ';
 althtmldef "assIntOp" as ' assIntOp ';
 latexdef "assIntOp" as "\mathrm{assIntOp}";
htmldef "MgmALT" as 'MgmALT';
 althtmldef "MgmALT" as 'MgmALT';
 latexdef "MgmALT" as "\mathrm{MgmALT}";
htmldef "CMgmALT" as 'CMgmALT';
 althtmldef "CMgmALT" as 'CMgmALT';
 latexdef "CMgmALT" as "\mathrm{CMgmALT}";
htmldef "SGrpALT" as 'SGrpALT';
 althtmldef "SGrpALT" as 'SGrpALT';
 latexdef "SGrpALT" as "\mathrm{SGrpALT}";
htmldef "CSGrpALT" as 'CSGrpALT';
 althtmldef "CSGrpALT" as 'CSGrpALT';
 latexdef "CSGrpALT" as "\mathrm{CSGrpALT}";
htmldef "RngCatALTV" as 'RngCatALTV';
 althtmldef "RngCatALTV" as 'RngCatALTV';
 latexdef "RngCatALTV" as "\mathrm{RngCatALTV}";
htmldef "RingCatALTV" as 'RingCatALTV';
 althtmldef "RingCatALTV" as 'RingCatALTV';
 latexdef "RingCatALTV" as "\mathrm{RingCatALTV}";
htmldef "PrmRing" as
  "<IMG SRC='_prring.gif' WIDTH=45 HEIGHT=19 ALT=' PrmRing' TITLE='PrmRing'>";
  althtmldef "PrmRing" as "PrmRing";
  latexdef "PrmRing" as "\mathrm{PrmRing}";
htmldef "DMatALT" as ' DMatALT ';
 althtmldef "DMatALT" as ' DMatALT ';
 latexdef "DMatALT" as "\mathrm{DMatALT}";
htmldef "ScMatALT" as ' ScMatALT ';
 althtmldef "ScMatALT" as ' ScMatALT ';
 latexdef "ScMatALT" as "\mathrm{ScMatALT}";
htmldef "linC" as ' linC ';
 althtmldef "linC" as ' linC ';
 latexdef "linC" as "\mathrm{linC}";
htmldef "LinCo" as ' LinCo ';
 althtmldef "LinCo" as ' LinCo ';
 latexdef "LinCo" as "\mathrm{LinCo}";
htmldef "linIndS" as ' linIndS ';
 althtmldef "linIndS" as ' linIndS ';
 latexdef "linIndS" as "\mathrm{linIndS}";
htmldef "linDepS" as ' linDepS ';
 althtmldef "linDepS" as ' linDepS ';
 latexdef "linDepS" as "\mathrm{linDepS}";
htmldef "/_f" as ' /_f ';
 althtmldef "/_f" as ' /<sub>f</sub> ';
 latexdef "/_f" as "\mathrm{/}_f";
htmldef "_O" as '_O';
 althtmldef "_O" as "&#x39F;";
 latexdef "_O" as "\mathrm{O}";
htmldef "#b" as '#b';
 althtmldef "#b" as '#<sub>b</sub>';
 latexdef "#b" as "\mathrm{\#}_b";
htmldef "digit" as 'digit';
 althtmldef "digit" as 'digit';
 latexdef "digit" as "\mathrm{digit}";
htmldef "-aryF" as '-aryF ';
 althtmldef "-aryF" as '-aryF ';
 latexdef "-aryF" as "\mathrm{-aryF}";
htmldef "IterComp" as 'IterComp';
 althtmldef "IterComp" as 'IterComp';
 latexdef "IterComp" as "\mathrm{IterComp}";
htmldef "Ack" as 'Ack';
 althtmldef "Ack" as 'Ack';
 latexdef "Ack" as "\mathrm{Ack}";
/* Elementary geometry (extension)  */
htmldef "LineM" as 'LineM';
 althtmldef "LineM" as 'Line<sub>M</sub>';
 latexdef "LineM" as "\mathrm{Line}_M";
htmldef "Sphere" as 'Sphere';
 althtmldef "Sphere" as 'Sphere';
 latexdef "Sphere" as "\mathrm{Sphere}";
/* End of Alexander van der Vekens's mathbox */

/* Mathbox of Zhi Wang */
htmldef "oppFunc" as " oppFunc ";
  althtmldef "oppFunc" as " oppFunc ";
  latexdef "oppFunc" as "\mathrm{oppFunc}";
htmldef "UP" as " UP ";
  althtmldef "UP" as " UP ";
  latexdef "UP" as "\mathbin{\operatorname{UP}}";
htmldef "swapF" as ' swap<sub><i>F</i></sub> ';
  althtmldef "swapF" as ' swap<sub><i>F</i></sub> ';
  latexdef "swapF" as "\mathrm{swap}_F";
htmldef "o.F" as
    " <IMG SRC='circ.gif' WIDTH=8 HEIGHT=19 ALT=' o.' TITLE='o.'>" +
    "<sub><i>F</i></sub> ";
  althtmldef "o.F" as ' &#8728;<sub><i>F</i></sub> ';
  latexdef "o.F" as "\circ_{F}";
htmldef "-o.F" as
    " <IMG SRC='minus.gif' WIDTH=11 HEIGHT=19 ALT=' -' TITLE='-'>" +
    "<IMG SRC='circ.gif' WIDTH=8 HEIGHT=19 ALT='o.' TITLE='o.'>" +
    "<sub><i>F</i></sub> ";
  althtmldef "-o.F" as ' &minus;&#8728;<sub><i>F</i></sub> ';
  latexdef "-o.F" as "-\circ_{F}";
htmldef "ThinCat" as "ThinCat";
  althtmldef "ThinCat" as "ThinCat";
  latexdef "ThinCat" as "\mathrm{ThinCat}";
htmldef "TermCat" as "TermCat";
  althtmldef "TermCat" as "TermCat";
  latexdef "TermCat" as "\mathrm{TermCat}";
htmldef "ProsetToCat" as "ProsetToCat";
  althtmldef "ProsetToCat" as "ProsetToCat";
  latexdef "ProsetToCat" as "\mathrm{ProsetToCat}";
htmldef "MndToCat" as "MndToCat";
  althtmldef "MndToCat" as "MndToCat";
  latexdef "MndToCat" as "\mathrm{MndToCat}";
htmldef "Lan" as " Lan ";
  althtmldef "Lan" as " Lan ";
  latexdef "Lan" as "\mathrm{Lan}";
htmldef "Ran" as " Ran ";
  althtmldef "Ran" as " Ran ";
  latexdef "Ran" as "\mathrm{Ran}";
htmldef "Limit" as " Limit ";
  althtmldef "Limit" as " Limit ";
  latexdef "Limit" as "\mathrm{Limit}";
htmldef "Colimit" as " Colimit ";
  althtmldef "Colimit" as " Colimit ";
  latexdef "Colimit" as "\mathrm{Colimit}";
/* End of Zhi Wang's mathbox */

/* Mathbox of Emmett Weisz */
htmldef "setrecs" as "setrecs";
  althtmldef "setrecs" as "setrecs";
  latexdef "setrecs" as "\mathrm{setrecs}";
htmldef "Pg" as "Pg";
  althtmldef "Pg" as "Pg";
  latexdef "Pg" as "\mathrm{Pg}";
/* End of Emmett Weisz's mathbox */

/* Mathbox of David A. Wheeler */
htmldef ">_" as
    " <IMG SRC='ge.gif' WIDTH=11 HEIGHT=19 ALT=' &gt;_' TITLE='&gt;_'> ";
  althtmldef ">_" as ' &ge; ';
  latexdef ">_" as "\ge";
htmldef ">" as
    " <IMG SRC='gt.gif' WIDTH=11 HEIGHT=19 ALT=' &gt;' TITLE='&gt;'> ";
  althtmldef ">" as ' &gt; ';
  latexdef ">" as ">";
/*
htmldef "sinh" as
    "<IMG SRC='_sinh.gif' WIDTH=20 HEIGHT=19 ALT=' sinh' TITLE='sinh'>";
*/
htmldef "sinh" as "sinh";
  althtmldef "sinh" as "sinh";
  latexdef "sinh" as "\sinh";
/*
htmldef "cosh" as
    "<IMG SRC='_cosh.gif' WIDTH=20 HEIGHT=19 ALT=' cosh' TITLE='cosh'>";
*/
htmldef "cosh" as "cosh";
  althtmldef "cosh" as "cosh";
  latexdef "cosh" as "\cosh";
/*
htmldef "tanh" as
    "<IMG SRC='_tanh.gif' WIDTH=20 HEIGHT=19 ALT=' tanh' TITLE='tanh'>";
*/
htmldef "tanh" as "tanh";
  althtmldef "tanh" as "tanh";
  latexdef "tanh" as "\tanh";
htmldef "sec" as
    "<IMG SRC='_sec.gif' WIDTH=20 HEIGHT=19 ALT=' sec' TITLE='sec'>";
  althtmldef "sec" as "sec";
  latexdef "sec" as "\sec";
htmldef "csc" as
    "<IMG SRC='_csc.gif' WIDTH=20 HEIGHT=19 ALT=' csc' TITLE='csc'>";
  althtmldef "csc" as "csc";
  latexdef "csc" as "\csc";
htmldef "cot" as
    "<IMG SRC='_cot.gif' WIDTH=20 HEIGHT=19 ALT=' cot' TITLE='cot'>";
  althtmldef "cot" as "cot";
  latexdef "cot" as "\cot";
/*
htmldef "_" as
    "<IMG SRC='underscore.gif' WIDTH=20 HEIGHT=19 ALT=' _' TITLE='_'>";
*/
htmldef "_" as '<FONT COLOR="#808080">_</FONT>';
  althtmldef "_" as '<SPAN CLASS=hidden STYLE="color:gray">_</SPAN>';
  latexdef "_" as "\_";
htmldef "." as
    "<IMG SRC='period.gif' WIDTH=20 HEIGHT=19 ALT=' period' TITLE='period'>";
  althtmldef "." as ".";
  latexdef "." as ".";
htmldef "log_" as "log_";
  althtmldef "log_" as "log_";
  latexdef "log_" as "\operatorname{\underline{log}}";
htmldef "AE" as
  "<IMG SRC='forall.gif' WIDTH=10 HEIGHT=19 ALT=' A.' TITLE='A.'>" +
  "<IMG SRC='exists.gif' WIDTH=9 HEIGHT=19 ALT='E.' TITLE='E.'>";
  althtmldef "AE" as '&forall;&exist;'; /* &#8704;&#8707; */
  latexdef "AE" as "\forall\exists";
htmldef "Reflexive" as "Reflexive";
  althtmldef "Reflexive" as "Reflexive";
  latexdef "Reflexive" as "\mathrel{\operatorname{Reflexive}}";
htmldef "Irreflexive" as "Irreflexive";
  althtmldef "Irreflexive" as "Irreflexive";
  latexdef "Irreflexive" as "\mathrel{\operatorname{Irreflexive}}";
/* End of David A. Wheeler's mathbox */

/* Mathbox of Alan Sare */
htmldef "(." as
    "<IMG SRC='period.gif' WIDTH=4 HEIGHT=19 ALT=' (.' TITLE='(.'>";
althtmldef "(." as
'<SPAN STYLE="color:#00CD00">&#40;&#160;&#160;&#160;</SPAN>';
/* This puts 0 white spaces before the left parenthesis(&#40) and 3 white
   spaces after. Here the parenthesis shall be colored bright green, the same
   color as the arrow. Here we are trying to use green parentheses instead of
   green periods. The reasoning is that parenthesis are better because they are
   more consistent with
   a) conventional Metamath notation so the User understands it better;
   b) Because these parentheses are now bright green, that sufficiently
   distinguishes these parentheses from the parentheses used to parse the
   wffs. The green parentheses are notation of the Virtual Deduction "mediator"
   notation. */
latexdef "(." as ".";
htmldef ")." as
    "<IMG SRC='period.gif' WIDTH=4 HEIGHT=19 ALT=' ).' TITLE=').'>";
althtmldef ")." as
'<SPAN STYLE="color:#00CD00">&#160;&#160;&#160;&#41;</SPAN>';
/* This puts 3 white spaces before the right parenthesis(&#41) and 0 white
   spaces after. Here the parenthesis shall be colored bright green, the same
   color as the arrow. Here we are trying to use green parentheses instead of
   green periods. The reasoning is that parenthesis are better because its more
   consistent
   with a) conventional set.mm notation so the User understands it better;
   b) Because these parentheses are now bright green, that sufficiently
   distinguishes these parentheses from the parentheses used to parse the
   wffs. The green parentheses are notation of the Virtual Deduction "mediator"
   notation. */
latexdef ")." as ".";
htmldef "->." as " <IMG SRC='blacktriangleright.gif' " +
    "WIDTH=11 HEIGHT=19 ALT=' -&gt;.' TITLE='-&gt;.'> ";
althtmldef "->." as
  '<SPAN STYLE="color:#00CD00"><FONT FACE=veranda>' +
  '&#160;&#160;&#160;&#9654;&#160;&#160;&#160;</FONT></SPAN>';
/* This should work better than the one above because we put white spaces
   around the arrow. It is better with an equal number of white spaces on each
   side of the arrow. The bright green for the virtual deduction notation
   works well. */
latexdef "->." as "\blacktriangleright";
htmldef "->.." as " <IMG SRC='__tobold.gif' " +
    "WIDTH=15 HEIGHT=19 ALT=' -&gt;..' TITLE='-&gt;..'> ";
  althtmldef "->.." as " <B>&rarr;</B> ";
  latexdef "->.." as "\pmb{\rightarrow}";
htmldef ",." as
    "<IMG SRC='comma.gif' WIDTH=4 HEIGHT=19 ALT=' ,.' TITLE=',.'>";
althtmldef ",." as
    '<SPAN STYLE="color:#00CD00"><FONT SIZE=4>' +
    '&#160;&#160;&#160;&#44;&#160;&#160;&#160;</FONT></SPAN>';
/* This color is green3. It is brighter and lighter than Irish flag. It is
   bright enough to stand out and it is not too light
   to be seen. It is clearly distinguishable from black. */
latexdef ",." as " , ";
/* End of Alan Sare's mathbox */

/* Mathbox of ML */
htmldef "^^" as "<IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 " +
                "ALT=' ^^' TITLE='^^'>" +
                "<IMG SRC='uparrow.gif' WIDTH=7 HEIGHT=19 " +
                "ALT=' ^^' TITLE='^^'>";
  althtmldef "^^" as '&uarr;&uarr;';
  latexdef "^^" as "\uparrow\uparrow";
/* End of ML's mathbox */

/* Mathbox of Jonathan Ben-Naim */
htmldef "ph'" as "<IMG SRC='_bnj_phiPrime.gif'   WIDTH=15 HEIGHT=19" +
       " ALT=" + '"' + " ph'" + '"' + " TITLE=" + '"' + "ph'" + '"' + ">";
htmldef "ps'" as "<IMG SRC='_bnj_psiPrime.gif'   WIDTH=16 HEIGHT=19" +
       " ALT=" + '"' + " ps'" + '"' + " TITLE=" + '"' + "ps'" + '"' + ">";
htmldef "ch'" as "<IMG SRC='_bnj_chiPrime.gif'   WIDTH=16 HEIGHT=19" +
       " ALT=" + '"' + " ch'" + '"' + " TITLE=" + '"' + "ch'" + '"' + ">";
htmldef "th'" as "<IMG SRC='_bnj_thetaPrime.gif' WIDTH=12 HEIGHT=19" +
       " ALT=" + '"' + " th'" + '"' + " TITLE=" + '"' + "th'" + '"' + ">";
htmldef "ta'" as "<IMG SRC='_bnj_tauPrime.gif'   WIDTH=14 HEIGHT=19" +
       " ALT=" + '"' + " ta'" + '"' + " TITLE=" + '"' + "ta'" + '"' + ">";
htmldef "et'" as "<IMG SRC='_bnj_etaPrime.gif'   WIDTH=13 HEIGHT=19" +
       " ALT=" + '"' + " et'" + '"' + " TITLE=" + '"' + "et'" + '"' + ">";
htmldef "ze'" as "<IMG SRC='_bnj_zetaPrime.gif'  WIDTH=13 HEIGHT=19" +
       " ALT=" + '"' + " ze'" + '"' + " TITLE=" + '"' + "ze'" + '"' + ">";
htmldef "si'" as "<IMG SRC='_bnj_sigmaPrime.gif' WIDTH=14 HEIGHT=19" +
       " ALT=" + '"' + " si'" + '"' + " TITLE=" + '"' + "si'" + '"' + ">";
htmldef "rh'" as "<IMG SRC='_bnj_rhoPrime.gif'   WIDTH=13 HEIGHT=19" +
       " ALT=" + '"' + " rh'" + '"' + " TITLE=" + '"' + "rh'" + '"' + ">";
althtmldef "ph'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D711;&prime;</SPAN>';
althtmldef "ps'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D713;&prime;</SPAN>';
althtmldef "ch'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D712;&prime;</SPAN>';
althtmldef "th'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D703;&prime;</SPAN>';
althtmldef "ta'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70F;&prime;</SPAN>';
althtmldef "et'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D702;&prime;</SPAN>';
althtmldef "ze'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D701;&prime;</SPAN>';
althtmldef "si'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70E;&prime;</SPAN>';
althtmldef "rh'" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70C;&prime;</SPAN>';
latexdef "ph'" as "\varphi'";
latexdef "ps'" as "\psi'";
latexdef "ch'" as "\chi'";
latexdef "th'" as "\theta'";
latexdef "ta'" as "\tau'";
latexdef "et'" as "\eta'";
latexdef "ze'" as "\zeta'";
latexdef "si'" as "\sigma'";
latexdef "rh'" as "\rho'";
htmldef 'ph"' as "<IMG SRC='_bnj_phiPrimePrime.gif'   WIDTH=18 HEIGHT=19" +
      " ALT=' ph" + '"' + "' TITLE='ph" + '"' + "'>";
htmldef 'ps"' as "<IMG SRC='_bnj_psiPrimePrime.gif'   WIDTH=19 HEIGHT=19" +
      " ALT=' ps" + '"' + "' TITLE='ps" + '"' + "'>";
htmldef 'ch"' as "<IMG SRC='_bnj_chiPrimePrime.gif'   WIDTH=19 HEIGHT=19" +
      " ALT=' ch" + '"' + "' TITLE='ch" + '"' + "'>";
htmldef 'th"' as "<IMG SRC='_bnj_thetaPrimePrime.gif' WIDTH=15 HEIGHT=19" +
      " ALT=' th" + '"' + "' TITLE='th" + '"' + "'>";
htmldef 'ta"' as "<IMG SRC='_bnj_tauPrimePrime.gif'   WIDTH=17 HEIGHT=19" +
      " ALT=' ta" + '"' + "' TITLE='ta" + '"' + "'>";
htmldef 'et"' as "<IMG SRC='_bnj_etaPrimePrime.gif'   WIDTH=16 HEIGHT=19" +
      " ALT=' et" + '"' + "' TITLE='et" + '"' + "'>";
htmldef 'ze"' as "<IMG SRC='_bnj_zetaPrimePrime.gif'  WIDTH=16 HEIGHT=19" +
      " ALT=' ze" + '"' + "' TITLE='ze" + '"' + "'>";
htmldef 'si"' as "<IMG SRC='_bnj_sigmaPrimePrime.gif' WIDTH=17 HEIGHT=19" +
      " ALT=' si" + '"' + "' TITLE='si" + '"' + "'>";
htmldef 'rh"' as "<IMG SRC='_bnj_rhoPrimePrime.gif'   WIDTH=16 HEIGHT=19" +
      " ALT=' rh" + '"' + "' TITLE='rh" + '"' + "'>";
althtmldef 'ph"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D711;&Prime;</SPAN>';
althtmldef 'ps"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D713;&Prime;</SPAN>';
althtmldef 'ch"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D712;&Prime;</SPAN>';
althtmldef 'th"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D703;&Prime;</SPAN>';
althtmldef 'ta"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70F;&Prime;</SPAN>';
althtmldef 'et"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D702;&Prime;</SPAN>';
althtmldef 'ze"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D701;&Prime;</SPAN>';
althtmldef 'si"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70E;&Prime;</SPAN>';
althtmldef 'rh"' as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70C;&Prime;</SPAN>';
latexdef 'ph"' as "\varphi''";
latexdef 'ps"' as "\psi''";
latexdef 'ch"' as "\chi''";
latexdef 'th"' as "\theta''";
latexdef 'ta"' as "\tau''";
latexdef 'et"' as "\eta''";
latexdef 'ze"' as "\zeta''";
latexdef 'si"' as "\sigma''";
latexdef 'rh"' as "\rho''";
htmldef "ph0"  as "<IMG SRC='_bnj_phi0.gif'   WIDTH=18 HEIGHT=19" +
    " ALT=' ph0' TITLE='ph0'>";
htmldef "ps0"  as "<IMG SRC='_bnj_psi0.gif'   WIDTH=19 HEIGHT=19" +
    " ALT=' ps0' TITLE='ps0'>";
htmldef "ch0_" as "<IMG SRC='_bnj_chi0.gif'   WIDTH=19 HEIGHT=19" +
    " ALT=' ch0_' TITLE='ch0_'>";
htmldef "th0"  as "<IMG SRC='_bnj_theta0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' th0' TITLE='th0'>";
htmldef "ta0"  as "<IMG SRC='_bnj_tau0.gif'   WIDTH=17 HEIGHT=19" +
    " ALT=' ta0' TITLE='ta0'>";
htmldef "et0"  as "<IMG SRC='_bnj_eta0.gif'   WIDTH=16 HEIGHT=19" +
    " ALT=' et0' TITLE='et0'>";
htmldef "ze0"  as "<IMG SRC='_bnj_zeta0.gif'  WIDTH=16 HEIGHT=19" +
    " ALT=' ze0' TITLE='ze0'>";
htmldef "si0"  as "<IMG SRC='_bnj_sigma0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' si0' TITLE='si0'>";
htmldef "rh0"  as "<IMG SRC='_bnj_rho0.gif'   WIDTH=16 HEIGHT=19" +
    " ALT=' rh0' TITLE='rh0'>";
althtmldef "ph0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D711;<SUB>0</SUB></SPAN>';
althtmldef "ps0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D713;<SUB>0</SUB></SPAN>';
althtmldef "ch0_" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D712;<SUB>0</SUB></SPAN>';
althtmldef "th0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D703;<SUB>0</SUB></SPAN>';
althtmldef "ta0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70F;<SUB>0</SUB></SPAN>';
althtmldef "et0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D702;<SUB>0</SUB></SPAN>';
althtmldef "ze0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D701;<SUB>0</SUB></SPAN>';
althtmldef "si0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70E;<SUB>0</SUB></SPAN>';
althtmldef "rh0"  as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70C;<SUB>0</SUB></SPAN>';
latexdef "ph0"  as "\varphi_0";
latexdef "ps0"  as "\psi_0";
latexdef "ch0_" as "\chi_0";
latexdef "th0"  as "\theta_0";
latexdef "ta0"  as "\tau_0";
latexdef "et0"  as "\eta_0";
latexdef "ze0"  as "\zeta_0";
latexdef "si0"  as "\sigma_0";
latexdef "rh0"  as "\rho_0";
htmldef "ph1" as "<IMG SRC='_bnj_phi1.gif'   WIDTH=16 HEIGHT=19" +
    " ALT=' ph1' TITLE='ph1'>";
htmldef "ps1" as "<IMG SRC='_bnj_psi1.gif'   WIDTH=17 HEIGHT=19" +
    " ALT=' ps1' TITLE='ps1'>";
htmldef "ch1" as "<IMG SRC='_bnj_chi1.gif'   WIDTH=17 HEIGHT=19" +
    " ALT=' ch1' TITLE='ch1'>";
htmldef "th1" as "<IMG SRC='_bnj_theta1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' th1' TITLE='th1'>";
htmldef "ta1" as "<IMG SRC='_bnj_tau1.gif'   WIDTH=15 HEIGHT=19" +
    " ALT=' ta1' TITLE='ta1'>";
htmldef "et1" as "<IMG SRC='_bnj_eta1.gif'   WIDTH=14 HEIGHT=19" +
    " ALT=' et1' TITLE='et1'>";
htmldef "ze1" as "<IMG SRC='_bnj_zeta1.gif'  WIDTH=14 HEIGHT=19" +
    " ALT=' ze1' TITLE='ze1'>";
htmldef "si1" as "<IMG SRC='_bnj_sigma1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' si1' TITLE='si1'>";
htmldef "rh1" as "<IMG SRC='_bnj_rho1.gif'   WIDTH=14 HEIGHT=19" +
    " ALT=' rh1' TITLE='rh1'>";
althtmldef "ph1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D711;<SUB>1</SUB></SPAN>';
althtmldef "ps1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D713;<SUB>1</SUB></SPAN>';
althtmldef "ch1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D712;<SUB>1</SUB></SPAN>';
althtmldef "th1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D703;<SUB>1</SUB></SPAN>';
althtmldef "ta1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70F;<SUB>1</SUB></SPAN>';
althtmldef "et1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D702;<SUB>1</SUB></SPAN>';
althtmldef "ze1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D701;<SUB>1</SUB></SPAN>';
althtmldef "si1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70E;<SUB>1</SUB></SPAN>';
althtmldef "rh1" as
    '<SPAN CLASS=wff STYLE="color:blue">&#x1D70C;<SUB>1</SUB></SPAN>';
latexdef "ph1" as "\varphi_1";
latexdef "ps1" as "\psi_1";
latexdef "ch1" as "\chi_1";
latexdef "th1" as "\theta_1";
latexdef "ta1" as "\tau_1";
latexdef "et1" as "\eta_1";
latexdef "ze1" as "\zeta_1";
latexdef "si1" as "\sigma_1";
latexdef "rh1" as "\rho_1";
htmldef "a'" as "<IMG SRC='_bnj_aPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " a'" + '"' + " TITLE=" + '"' + "a'" + '"' + ">";
htmldef "b'" as "<IMG SRC='_bnj_bPrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " b'" + '"' + " TITLE=" + '"' + "b'" + '"' + ">";
htmldef "c'" as "<IMG SRC='_bnj_cPrime.gif' WIDTH=11 HEIGHT=19" +
    " ALT=" + '"' + " c'" + '"' + " TITLE=" + '"' + "c'" + '"' + ">";
htmldef "d'" as "<IMG SRC='_bnj_dPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " d'" + '"' + " TITLE=" + '"' + "d'" + '"' + ">";
htmldef "e'" as "<IMG SRC='_bnj_ePrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " e'" + '"' + " TITLE=" + '"' + "e'" + '"' + ">";
htmldef "f'" as "<IMG SRC='_bnj_fPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " f'" + '"' + " TITLE=" + '"' + "f'" + '"' + ">";
htmldef "g'" as "<IMG SRC='_bnj_gPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " g'" + '"' + " TITLE=" + '"' + "g'" + '"' + ">";
htmldef "h'" as "<IMG SRC='_bnj_hPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " h'" + '"' + " TITLE=" + '"' + "h'" + '"' + ">";
htmldef "i'" as "<IMG SRC='_bnj_iPrime.gif' WIDTH=10 HEIGHT=19" +
    " ALT=" + '"' + " i'" + '"' + " TITLE=" + '"' + "i'" + '"' + ">";
htmldef "j'" as "<IMG SRC='_bnj_jPrime.gif' WIDTH=11 HEIGHT=19" +
    " ALT=" + '"' + " j'" + '"' + " TITLE=" + '"' + "j'" + '"' + ">";
htmldef "k'" as "<IMG SRC='_bnj_kPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " k'" + '"' + " TITLE=" + '"' + "k'" + '"' + ">";
htmldef "l'" as "<IMG SRC='_bnj_lPrime.gif' WIDTH=9  HEIGHT=19" +
    " ALT=" + '"' + " l'" + '"' + " TITLE=" + '"' + "l'" + '"' + ">";
htmldef "m'" as "<IMG SRC='_bnj_mPrime.gif' WIDTH=18 HEIGHT=19" +
    " ALT=" + '"' + " m'" + '"' + " TITLE=" + '"' + "m'" + '"' + ">";
htmldef "n'" as "<IMG SRC='_bnj_nPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " n'" + '"' + " TITLE=" + '"' + "n'" + '"' + ">";
htmldef "o'_" as "<IMG SRC='_bnj_oPrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " o'_" + '"' + " TITLE=" + '"' + "o'_" + '"' + ">";
htmldef "p'" as "<IMG SRC='_bnj_pPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " p'" + '"' + " TITLE=" + '"' + "p'" + '"' + ">";
htmldef "q'" as "<IMG SRC='_bnj_qPrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " q'" + '"' + " TITLE=" + '"' + "q'" + '"' + ">";
htmldef "r'" as "<IMG SRC='_bnj_rPrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " r'" + '"' + " TITLE=" + '"' + "r'" + '"' + ">";
htmldef "s'_" as "<IMG SRC='_bnj_sPrime.gif' WIDTH=11 HEIGHT=19" +
    " ALT=" + '"' + " s'" + '"' + " TITLE=" + '"' + "s'" + '"' + ">";
htmldef "t'" as "<IMG SRC='_bnj_tPrime.gif' WIDTH=11 HEIGHT=19" +
    " ALT=" + '"' + " t'" + '"' + " TITLE=" + '"' + "t'" + '"' + ">";
htmldef "u'" as "<IMG SRC='_bnj_uPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " u'" + '"' + " TITLE=" + '"' + "u'" + '"' + ">";
htmldef "v'_" as "<IMG SRC='_bnj_vPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " v'" + '"' + " TITLE=" + '"' + "v'" + '"' + ">";
htmldef "w'" as "<IMG SRC='_bnj_wPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " w'" + '"' + " TITLE=" + '"' + "w'" + '"' + ">";
htmldef "x'" as "<IMG SRC='_bnj_xPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " x'" + '"' + " TITLE=" + '"' + "x'" + '"' + ">";
htmldef "y'" as "<IMG SRC='_bnj_yPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " y'" + '"' + " TITLE=" + '"' + "y'" + '"' + ">";
htmldef "z'" as "<IMG SRC='_bnj_zPrime.gif' WIDTH=13 HEIGHT=19" +
    " ALT=" + '"' + " z'" + '"' + " TITLE=" + '"' + "z'" + '"' + ">";
althtmldef "a'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D44E;&prime;</SPAN>';
althtmldef "b'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D44F;&prime;</SPAN>';
althtmldef "c'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D450;&prime;</SPAN>';
althtmldef "d'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D451;&prime;</SPAN>';
althtmldef "e'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D452;&prime;</SPAN>';
althtmldef "f'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D453;&prime;</SPAN>';
althtmldef "g'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D454;&prime;</SPAN>';
althtmldef "h'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x210E;&prime;</SPAN>';
althtmldef "i'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D456;&prime;</SPAN>';
althtmldef "j'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D457;&prime;</SPAN>';
althtmldef "k'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D458;&prime;</SPAN>';
althtmldef "l'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D459;&prime;</SPAN>';
althtmldef "m'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45A;&prime;</SPAN>';
althtmldef "n'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45B;&prime;</SPAN>';
althtmldef "o'_" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45C;&prime;</SPAN>';
althtmldef "p'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45D;&prime;</SPAN>';
althtmldef "q'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45E;&prime;</SPAN>';
althtmldef "r'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45F;&prime;</SPAN>';
althtmldef "s'_" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D460;&prime;</SPAN>';
althtmldef "t'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D461;&prime;</SPAN>';
althtmldef "u'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D462;&prime;</SPAN>';
althtmldef "v'_" as
     '<SPAN CLASS=setvar STYLE="color:red">&#x1D463;&prime;</SPAN>';
althtmldef "w'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D464;&prime;</SPAN>';
althtmldef "x'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D465;&prime;</SPAN>';
althtmldef "y'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D466;&prime;</SPAN>';
althtmldef "z'" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D467;&prime;</SPAN>';
latexdef "a'" as "a'";
latexdef "b'" as "b'";
latexdef "c'" as "c'";
latexdef "d'" as "d'";
latexdef "e'" as "e'";
latexdef "f'" as "f'";
latexdef "g'" as "g'";
latexdef "h'" as "h'";
latexdef "i'" as "i'";
latexdef "j'" as "j'";
latexdef "k'" as "k'";
latexdef "l'" as "l'";
latexdef "m'" as "m'";
latexdef "n'" as "n'";
latexdef "o'_" as "o'";
latexdef "p'" as "p'";
latexdef "q'" as "q'";
latexdef "r'" as "r'";
latexdef "s'_" as "s'";
latexdef "t'" as "t'";
latexdef "u'" as "u'";
latexdef "v'_" as "v'";
latexdef "w'" as "w'";
latexdef "x'" as "x'";
latexdef "y'" as "y'";
latexdef "z'" as "z'";
htmldef 'a"' as "<IMG SRC='_bnj_aPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' a" + '"' + "' TITLE='a" + '"' + "'>";
htmldef 'b"' as "<IMG SRC='_bnj_bPrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' b" + '"' + "' TITLE='b" + '"' + "'>";
htmldef 'c"' as "<IMG SRC='_bnj_cPrimePrime.gif' WIDTH=14 HEIGHT=19 " +
      " ALT=' c" + '"' + "' TITLE='c" + '"' + "'>";
htmldef 'd"' as "<IMG SRC='_bnj_dPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' d" + '"' + "' TITLE='d" + '"' + "'>";
htmldef 'e"' as "<IMG SRC='_bnj_ePrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' e" + '"' + "' TITLE='e" + '"' + "'>";
htmldef 'f"' as "<IMG SRC='_bnj_fPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' f" + '"' + "' TITLE='f" + '"' + "'>";
htmldef 'g"' as "<IMG SRC='_bnj_gPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' g" + '"' + "' TITLE='g" + '"' + "'>";
htmldef 'h"' as "<IMG SRC='_bnj_hPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' h" + '"' + "'TITLE='h" + '"' + "'>";
htmldef 'i"' as "<IMG SRC='_bnj_iPrimePrime.gif' WIDTH=13 HEIGHT=19 " +
      " ALT=' i" + '"' + "' TITLE='i" + '"' + "'>";
htmldef 'j"' as "<IMG SRC='_bnj_jPrimePrime.gif' WIDTH=14 HEIGHT=19 " +
      " ALT=' j" + '"' + "' TITLE='j" + '"' + "'>";
htmldef 'k"' as "<IMG SRC='_bnj_kPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' k" + '"' + "' TITLE='k" + '"' + "'>";
htmldef 'l"' as "<IMG SRC='_bnj_lPrimePrime.gif' WIDTH=12 HEIGHT=19 " +
      " ALT=' l" + '"' + "'TITLE='l" + '"' + "'>";
htmldef 'm"' as "<IMG SRC='_bnj_mPrimePrime.gif' WIDTH=21 HEIGHT=19 " +
      " ALT=' m" + '"' + "' TITLE='m" + '"' + "'>";
htmldef 'n"' as "<IMG SRC='_bnj_nPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' n" + '"' + "' TITLE='n" + '"' + "'>";
htmldef 'o"_' as "<IMG SRC='_bnj_oPrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' o" + '"' + "'TITLE='o" + '"' + "'>";
htmldef 'p"' as "<IMG SRC='_bnj_pPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' p" + '"' + "'TITLE='p" + '"' + "'>";
htmldef 'q"' as "<IMG SRC='_bnj_qPrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' q" + '"' + "'TITLE='q" + '"' + "'>";
htmldef 'r"' as "<IMG SRC='_bnj_rPrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' r" + '"' + "'TITLE='r" + '"' + "'>";
htmldef 's"_' as "<IMG SRC='_bnj_sPrimePrime.gif' WIDTH=14 HEIGHT=19 " +
      " ALT=' s" + '"' + "'TITLE='s" + '"' + "'>";
htmldef 't"' as "<IMG SRC='_bnj_tPrimePrime.gif' WIDTH=14 HEIGHT=19 " +
      " ALT=' t" + '"' + "'TITLE='t" + '"' + "'>";
htmldef 'u"' as "<IMG SRC='_bnj_uPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' u" + '"' + "'TITLE='u" + '"' + "'>";
htmldef 'v"_' as "<IMG SRC='_bnj_vPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' v" + '"' + "'TITLE='v" + '"' + "'>";
htmldef 'w"' as "<IMG SRC='_bnj_wPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' w" + '"' + "'TITLE='w" + '"' + "'>";
htmldef 'x"' as "<IMG SRC='_bnj_xPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' x" + '"' + "'TITLE='x" + '"' + "'>";
htmldef 'y"' as "<IMG SRC='_bnj_yPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' y" + '"' + "'TITLE='y" + '"' + "'>";
htmldef 'z"' as "<IMG SRC='_bnj_zPrimePrime.gif' WIDTH=16 HEIGHT=19 " +
      " ALT=' z" + '"' + "'TITLE='z" + '"' + "'>";
althtmldef 'a"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D44E;&Prime;</SPAN>';
althtmldef 'b"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D44F;&Prime;</SPAN>';
althtmldef 'c"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D450;&Prime;</SPAN>';
althtmldef 'd"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D451;&Prime;</SPAN>';
althtmldef 'e"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D452;&Prime;</SPAN>';
althtmldef 'f"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D453;&Prime;</SPAN>';
althtmldef 'g"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D454;&Prime;</SPAN>';
althtmldef 'h"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x210E;&Prime;</SPAN>';
althtmldef 'i"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D456;&Prime;</SPAN>';
althtmldef 'j"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D457;&Prime;</SPAN>';
althtmldef 'k"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D458;&Prime;</SPAN>';
althtmldef 'l"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D459;&Prime;</SPAN>';
althtmldef 'm"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45A;&Prime;</SPAN>';
althtmldef 'n"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45B;&Prime;</SPAN>';
althtmldef 'o"_' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45C;&Prime;</SPAN>';
althtmldef 'p"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45D;&Prime;</SPAN>';
althtmldef 'q"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45E;&Prime;</SPAN>';
althtmldef 'r"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45F;&Prime;</SPAN>';
althtmldef 's"_' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D460;&Prime;</SPAN>';
althtmldef 't"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D461;&Prime;</SPAN>';
althtmldef 'u"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D462;&Prime;</SPAN>';
althtmldef 'v"_' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D463;&Prime;</SPAN>';
althtmldef 'w"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D464;&Prime;</SPAN>';
althtmldef 'x"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D465;&Prime;</SPAN>';
althtmldef 'y"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D466;&Prime;</SPAN>';
althtmldef 'z"' as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D467;&Prime;</SPAN>';
latexdef 'a"' as "a''";
latexdef 'b"' as "b''";
latexdef 'c"' as "c''";
latexdef 'd"' as "d''";
latexdef 'e"' as "e''";
latexdef 'f"' as "f''";
latexdef 'g"' as "g''";
latexdef 'h"' as "h''";
latexdef 'i"' as "i''";
latexdef 'j"' as "j''";
latexdef 'k"' as "k''";
latexdef 'l"' as "l''";
latexdef 'm"' as "m''";
latexdef 'n"' as "n''";
latexdef 'o"_' as "o''";
latexdef 'p"' as "p''";
latexdef 'q"' as "q''";
latexdef 'r"' as "r''";
latexdef 's"_' as "s''";
latexdef 't"' as "t''";
latexdef 'u"' as "u''";
latexdef 'v"_' as "v''";
latexdef 'w"' as "w''";
latexdef 'x"' as "x''";
latexdef 'y"' as "y''";
latexdef 'z"' as "z''";
htmldef "a0_"  as "<IMG SRC='_bnj_a0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' a0' TITLE='a0'>";
htmldef "b0_"  as "<IMG SRC='_bnj_b0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' b0' TITLE='b0'>";
htmldef "c0_" as "<IMG SRC='_bnj_c0.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' c0' TITLE='c0'>";
htmldef "d0"  as "<IMG SRC='_bnj_d0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' d0' TITLE='d0'>";
htmldef "e0"  as "<IMG SRC='_bnj_e0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' e0' TITLE='e0'>";
htmldef "f0_" as "<IMG SRC='_bnj_f0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' f0_' TITLE='f0_'>";
htmldef "g0"  as "<IMG SRC='_bnj_g0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' g0' TITLE='g0'>";
htmldef "h0"  as "<IMG SRC='_bnj_h0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' h0' TITLE='h0'>";
htmldef "i0"  as "<IMG SRC='_bnj_i0.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' i0' TITLE='i0'>";
htmldef "j0"  as "<IMG SRC='_bnj_j0.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' j0' TITLE='j0'>";
htmldef "k0"  as "<IMG SRC='_bnj_k0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' k0' TITLE='k0'>";
htmldef "l0"  as "<IMG SRC='_bnj_l0.gif' WIDTH=12 HEIGHT=19" +
    " ALT=' l0' TITLE='l0'>";
htmldef "m0"  as "<IMG SRC='_bnj_m0.gif' WIDTH=21 HEIGHT=19" +
    " ALT=' m0' TITLE='m0'>";
htmldef "n0_" as "<IMG SRC='_bnj_n0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' n0_' TITLE='n0_'>";
htmldef "o0_"  as "<IMG SRC='_bnj_o0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' o0_' TITLE='o0_'>";
htmldef "p0"  as "<IMG SRC='_bnj_p0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' p0' TITLE='p0'>";
htmldef "q0"  as "<IMG SRC='_bnj_q0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' q0' TITLE='q0'>";
htmldef "r0"  as "<IMG SRC='_bnj_r0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' r0' TITLE='r0'>";
htmldef "s0"  as "<IMG SRC='_bnj_s0.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' s0' TITLE='s0'>";
htmldef "t0"  as "<IMG SRC='_bnj_t0.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' t0' TITLE='t0'>";
htmldef "u0"  as "<IMG SRC='_bnj_u0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' u0' TITLE='u0'>";
htmldef "v0"  as "<IMG SRC='_bnj_v0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' v0' TITLE='v0'>";
htmldef "w0"  as "<IMG SRC='_bnj_w0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' w0' TITLE='w0'>";
htmldef "x0"  as "<IMG SRC='_bnj_x0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' x0' TITLE='x0'>";
htmldef "y0"  as "<IMG SRC='_bnj_y0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' y0' TITLE='y0'>";
htmldef "z0"  as "<IMG SRC='_bnj_z0.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' z0' TITLE='z0'>";
althtmldef "a0_"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D44E;<SUB>0</SUB></SPAN>';
althtmldef "b0_"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D44F;<SUB>0</SUB></SPAN>';
althtmldef "c0_" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D450;<SUB>0</SUB></SPAN>';
althtmldef "d0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D451;<SUB>0</SUB></SPAN>';
althtmldef "e0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D452;<SUB>0</SUB></SPAN>';
althtmldef "f0_" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D453;<SUB>0</SUB></SPAN>';
althtmldef "g0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D454;<SUB>0</SUB></SPAN>';
althtmldef "h0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x210E;<SUB>0</SUB></SPAN>';
althtmldef "i0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D456;<SUB>0</SUB></SPAN>';
althtmldef "j0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D457;<SUB>0</SUB></SPAN>';
althtmldef "k0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D458;<SUB>0</SUB></SPAN>';
althtmldef "l0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D459;<SUB>0</SUB></SPAN>';
althtmldef "m0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45A;<SUB>0</SUB></SPAN>';
althtmldef "n0_" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45B;<SUB>0</SUB></SPAN>';
althtmldef "o0_"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45C;<SUB>0</SUB></SPAN>';
althtmldef "p0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45D;<SUB>0</SUB></SPAN>';
althtmldef "q0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45E;<SUB>0</SUB></SPAN>';
althtmldef "r0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45F;<SUB>0</SUB></SPAN>';
althtmldef "s0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D460;<SUB>0</SUB></SPAN>';
althtmldef "t0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D461;<SUB>0</SUB></SPAN>';
althtmldef "u0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D462;<SUB>0</SUB></SPAN>';
althtmldef "v0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D463;<SUB>0</SUB></SPAN>';
althtmldef "w0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D464;<SUB>0</SUB></SPAN>';
althtmldef "x0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D465;<SUB>0</SUB></SPAN>';
althtmldef "y0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D466;<SUB>0</SUB></SPAN>';
althtmldef "z0"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D467;<SUB>0</SUB></SPAN>';
latexdef "a0_"  as "a_0";
latexdef "b0_"  as "b_0";
latexdef "c0_" as "c_0";
latexdef "d0"  as "d_0";
latexdef "e0"  as "e_0";
latexdef "f0_" as "f_0";
latexdef "g0"  as "g_0";
latexdef "h0"  as "h_0";
latexdef "i0"  as "i_0";
latexdef "j0"  as "j_0";
latexdef "k0"  as "k_0";
latexdef "l0"  as "l_0";
latexdef "m0"  as "m_0";
latexdef "n0_" as "n_0";
latexdef "o0_"  as "o_0";
latexdef "p0"  as "p_0";
latexdef "q0"  as "q_0";
latexdef "r0"  as "r_0";
latexdef "s0"  as "s_0";
latexdef "t0"  as "t_0";
latexdef "u0"  as "u_0";
latexdef "v0"  as "v_0";
latexdef "w0"  as "w_0";
latexdef "x0"  as "x_0";
latexdef "y0"  as "y_0";
latexdef "z0"  as "z_0";
htmldef "a1_"  as "<IMG SRC='_bnj_a1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' a1' TITLE='a1'>";
htmldef "b1_"  as "<IMG SRC='_bnj_b1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' b1' TITLE='b1'>";
htmldef "c1_" as "<IMG SRC='_bnj_c1.gif' WIDTH=12 HEIGHT=19" +
    " ALT=' c1_' TITLE='c1_'>";
htmldef "d1"  as "<IMG SRC='_bnj_d1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' d1' TITLE='d1'>";
htmldef "e1"  as "<IMG SRC='_bnj_e1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' e1' TITLE='e1'>";
htmldef "f1"  as "<IMG SRC='_bnj_f1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' f1' TITLE='f1'>";
htmldef "g1"  as "<IMG SRC='_bnj_g1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' g1' TITLE='g1'>";
htmldef "h1"  as "<IMG SRC='_bnj_h1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' h1' TITLE='h1'>";
htmldef "i1"  as "<IMG SRC='_bnj_i1.gif' WIDTH=11 HEIGHT=19" +
    " ALT=' i1' TITLE='i1'>";
htmldef "j1"  as "<IMG SRC='_bnj_j1.gif' WIDTH=12 HEIGHT=19" +
    " ALT=' j1' TITLE='j1'>";
htmldef "k1"  as "<IMG SRC='_bnj_k1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' k1' TITLE='k1'>";
htmldef "l1"  as "<IMG SRC='_bnj_l1.gif' WIDTH=10 HEIGHT=19" +
    " ALT=' l1' TITLE='l1'>";
htmldef "m1"  as "<IMG SRC='_bnj_m1.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' m1' TITLE='m1'>";
htmldef "n1"  as "<IMG SRC='_bnj_n1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' n1' TITLE='n1'>";
htmldef "o1_"  as "<IMG SRC='_bnj_o1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' o1_' TITLE='o1_'>";
htmldef "p1"  as "<IMG SRC='_bnj_p1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' p1' TITLE='p1'>";
htmldef "q1"  as "<IMG SRC='_bnj_q1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' q1' TITLE='q1'>";
htmldef "r1"  as "<IMG SRC='_bnj_r1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' r1' TITLE='r1'>";
htmldef "s1"  as "<IMG SRC='_bnj_s1.gif' WIDTH=12 HEIGHT=19" +
    " ALT=' s1' TITLE='s1'>";
htmldef "t1"  as "<IMG SRC='_bnj_t1.gif' WIDTH=12 HEIGHT=19" +
    " ALT=' t1' TITLE='t1'>";
htmldef "u1"  as "<IMG SRC='_bnj_u1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' u1' TITLE='u1'>";
htmldef "v1"  as "<IMG SRC='_bnj_v1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' v1' TITLE='v1'>";
htmldef "w1"  as "<IMG SRC='_bnj_w1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' w1' TITLE='w1'>";
htmldef "x1"  as "<IMG SRC='_bnj_x1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' x1' TITLE='x1'>";
htmldef "y1"  as "<IMG SRC='_bnj_y1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' y1' TITLE='y1'>";
htmldef "z1"  as "<IMG SRC='_bnj_z1.gif' WIDTH=14 HEIGHT=19" +
    " ALT=' z1' TITLE='z1'>";
althtmldef "a1_"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D44E;<SUB>1</SUB></SPAN>';
althtmldef "b1_"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D44F;<SUB>1</SUB></SPAN>';
althtmldef "c1_" as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D450;<SUB>1</SUB></SPAN>';
althtmldef "d1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D451;<SUB>1</SUB></SPAN>';
althtmldef "e1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D452;<SUB>1</SUB></SPAN>';
althtmldef "f1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D453;<SUB>1</SUB></SPAN>';
althtmldef "g1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D454;<SUB>1</SUB></SPAN>';
althtmldef "h1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x210E;<SUB>1</SUB></SPAN>';
althtmldef "i1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D456;<SUB>1</SUB></SPAN>';
althtmldef "j1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D457;<SUB>1</SUB></SPAN>';
althtmldef "k1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D458;<SUB>1</SUB></SPAN>';
althtmldef "l1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D459;<SUB>1</SUB></SPAN>';
althtmldef "m1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45A;<SUB>1</SUB></SPAN>';
althtmldef "n1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45B;<SUB>1</SUB></SPAN>';
althtmldef "o1_"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45C;<SUB>1</SUB></SPAN>';
althtmldef "p1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45D;<SUB>1</SUB></SPAN>';
althtmldef "q1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45E;<SUB>1</SUB></SPAN>';
althtmldef "r1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D45F;<SUB>1</SUB></SPAN>';
althtmldef "s1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D460;<SUB>1</SUB></SPAN>';
althtmldef "t1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D461;<SUB>1</SUB></SPAN>';
althtmldef "u1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D462;<SUB>1</SUB></SPAN>';
althtmldef "v1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D463;<SUB>1</SUB></SPAN>';
althtmldef "w1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D464;<SUB>1</SUB></SPAN>';
althtmldef "x1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D465;<SUB>1</SUB></SPAN>';
althtmldef "y1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D466;<SUB>1</SUB></SPAN>';
althtmldef "z1"  as
    '<SPAN CLASS=setvar STYLE="color:red">&#x1D467;<SUB>1</SUB></SPAN>';
latexdef "a1_"  as "a_1";
latexdef "b1_"  as "b_1";
latexdef "c1_" as "c_1";
latexdef "d1"  as "d_1";
latexdef "e1"  as "e_1";
latexdef "f1"  as "f_1";
latexdef "g1"  as "g_1";
latexdef "h1"  as "h_1";
latexdef "i1"  as "i_1";
latexdef "j1"  as "j_1";
latexdef "k1"  as "k_1";
latexdef "l1"  as "l_1";
latexdef "m1"  as "m_1";
latexdef "n1"  as "n_1";
latexdef "o1_"  as "o_1";
latexdef "p1"  as "p_1";
latexdef "q1"  as "q_1";
latexdef "r1"  as "r_1";
latexdef "s1"  as "s_1";
latexdef "t1"  as "t_1";
latexdef "u1"  as "u_1";
latexdef "v1"  as "v_1";
latexdef "w1"  as "w_1";
latexdef "x1"  as "x_1";
latexdef "y1"  as "y_1";
latexdef "z1"  as "z_1";
htmldef "A'" as "<IMG SRC='_bnj_caPrime.gif' WIDTH=15 HEIGHT=19" +
    " ALT=" + '"' + " A'" + '"' + " TITLE=" + '"' + "A'" + '"' + ">";
htmldef "B'" as "<IMG SRC='_bnj_cbPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " B'" + '"' + " TITLE=" + '"' + "B'" + '"' + ">";
htmldef "C'" as "<IMG SRC='_bnj_ccPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " C'" + '"' + " TITLE=" + '"' + "C'" + '"' + ">";
htmldef "D'" as "<IMG SRC='_bnj_cdPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " D'" + '"' + " TITLE=" + '"' + "D'" + '"' + ">";
htmldef "E'" as "<IMG SRC='_bnj_cePrime.gif' WIDTH=17 HEIGHT=19" +
    " ALT=" + '"' + " E'" + '"' + " TITLE=" + '"' + "E'" + '"' + ">";
htmldef "F'" as "<IMG SRC='_bnj_cfPrime.gif' WIDTH=17 HEIGHT=19" +
    " ALT=" + '"' + " F'" + '"' + " TITLE=" + '"' + "F'" + '"' + ">";
htmldef "G'" as "<IMG SRC='_bnj_cgPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " G'" + '"' + " TITLE=" + '"' + "G'" + '"' + ">";
htmldef "H'" as "<IMG SRC='_bnj_chPrime.gif' WIDTH=18 HEIGHT=19" +
    " ALT=" + '"' + " H'" + '"' + " TITLE=" + '"' + "H'" + '"' + ">";
htmldef "I'" as "<IMG SRC='_bnj_ciPrime.gif' WIDTH=12 HEIGHT=19" +
    " ALT=" + '"' + " I'" + '"' + " TITLE=" + '"' + "I'" + '"' + ">";
htmldef "J'" as "<IMG SRC='_bnj_cjPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " J'" + '"' + " TITLE=" + '"' + "J'" + '"' + ">";
htmldef "K'" as "<IMG SRC='_bnj_ckPrime.gif' WIDTH=18 HEIGHT=19" +
    " ALT=" + '"' + " K'" + '"' + " TITLE=" + '"' + "K'" + '"' + ">";
htmldef "L'" as "<IMG SRC='_bnj_clPrime.gif' WIDTH=14 HEIGHT=19" +
    " ALT=" + '"' + " L'" + '"' + " TITLE=" + '"' + "L'" + '"' + ">";
htmldef "M'" as "<IMG SRC='_bnj_cmPrime.gif' WIDTH=19 HEIGHT=19" +
    " ALT=" + '"' + " M'" + '"' + " TITLE=" + '"' + "M'" + '"' + ">";
htmldef "N'" as "<IMG SRC='_bnj_cnPrime.gif' WIDTH=18 HEIGHT=19" +
    " ALT=" + '"' + " N'" + '"' + " TITLE=" + '"' + "N'" + '"' + ">";
htmldef "O'" as "<IMG SRC='_bnj_coPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " O'" + '"' + " TITLE=" + '"' + "O'" + '"' + ">";
htmldef "P'" as "<IMG SRC='_bnj_cpPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " P'" + '"' + " TITLE=" + '"' + "P'" + '"' + ">";
htmldef "Q'" as "<IMG SRC='_bnj_cqPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " Q'" + '"' + " TITLE=" + '"' + "Q'" + '"' + ">";
htmldef "R'" as "<IMG SRC='_bnj_crPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " R'" + '"' + " TITLE=" + '"' + "R'" + '"' + ">";
htmldef "S'" as "<IMG SRC='_bnj_csPrime.gif' WIDTH=15 HEIGHT=19" +
    " ALT=" + '"' + " S'" + '"' + " TITLE=" + '"' + "S'" + '"' + ">";
htmldef "T'" as "<IMG SRC='_bnj_ctPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " T'" + '"' + " TITLE=" + '"' + "T'" + '"' + ">";
htmldef "U'" as "<IMG SRC='_bnj_cuPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " U'" + '"' + " TITLE=" + '"' + "U'" + '"' + ">";
htmldef "V'" as "<IMG SRC='_bnj_cvPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " V'" + '"' + " TITLE=" + '"' + "V'" + '"' + ">";
htmldef "W'" as "<IMG SRC='_bnj_cwPrime.gif' WIDTH=20 HEIGHT=19" +
    " ALT=" + '"' + " W'" + '"' + " TITLE=" + '"' + "W'" + '"' + ">";
htmldef "X'" as "<IMG SRC='_bnj_cxPrime.gif' WIDTH=17 HEIGHT=19" +
    " ALT=" + '"' + " X'" + '"' + " TITLE=" + '"' + "X'" + '"' + ">";
htmldef "Y'" as "<IMG SRC='_bnj_cyPrime.gif' WIDTH=16 HEIGHT=19" +
    " ALT=" + '"' + " Y'" + '"' + " TITLE=" + '"' + "Y'" + '"' + ">";
htmldef "Z'" as "<IMG SRC='_bnj_czPrime.gif' WIDTH=15 HEIGHT=19" +
    " ALT=" + '"' + " Z'" + '"' + " TITLE=" + '"' + "Z'" + '"' + ">";
althtmldef "A'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D434;&prime;</SPAN>';
althtmldef "B'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D435;&prime;</SPAN>';
althtmldef "C'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D436;&prime;</SPAN>';
althtmldef "D'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D437;&prime;</SPAN>';
althtmldef "E'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D438;&prime;</SPAN>';
althtmldef "F'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;&prime;</SPAN>';
althtmldef "G'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43A;&prime;</SPAN>';
althtmldef "H'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43B;&prime;</SPAN>';
althtmldef "I'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43C;&prime;</SPAN>';
althtmldef "J'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43D;&prime;</SPAN>';
althtmldef "K'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43E;&prime;</SPAN>';
althtmldef "L'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;&prime;</SPAN>';
althtmldef "M'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D440;&prime;</SPAN>';
althtmldef "N'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D441;&prime;</SPAN>';
althtmldef "O'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D442;&prime;</SPAN>';
althtmldef "P'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D443;&prime;</SPAN>';
althtmldef "Q'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D444;&prime;</SPAN>';
althtmldef "R'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D445;&prime;</SPAN>';
althtmldef "S'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D446;&prime;</SPAN>';
althtmldef "T'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D447;&prime;</SPAN>';
althtmldef "U'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D448;&prime;</SPAN>';
althtmldef "V'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;&prime;</SPAN>';
althtmldef "W'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44A;&prime;</SPAN>';
althtmldef "X'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44B;&prime;</SPAN>';
althtmldef "Y'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44C;&prime;</SPAN>';
althtmldef "Z'" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44D;&prime;</SPAN>';
latexdef "A'" as "A'";
latexdef "B'" as "B'";
latexdef "C'" as "C'";
latexdef "D'" as "D'";
latexdef "E'" as "E'";
latexdef "F'" as "F'";
latexdef "G'" as "G'";
latexdef "H'" as "H'";
latexdef "I'" as "I'";
latexdef "J'" as "J'";
latexdef "K'" as "K'";
latexdef "L'" as "L'";
latexdef "M'" as "M'";
latexdef "N'" as "N'";
latexdef "O'" as "O'";
latexdef "P'" as "P'";
latexdef "Q'" as "Q'";
latexdef "R'" as "R'";
latexdef "S'" as "S'";
latexdef "T'" as "T'";
latexdef "U'" as "U'";
latexdef "V'" as "V'";
latexdef "W'" as "W'";
latexdef "X'" as "X'";
latexdef "Y'" as "Y'";
latexdef "Z'" as "Z'";
htmldef 'A"' as "<IMG SRC='_bnj_caPrimePrime.gif' WIDTH=18 HEIGHT=19 " +
      " ALT=' A" + '"' + "'TITLE='A" + '"' + "'>";
htmldef 'B"' as "<IMG SRC='_bnj_cbPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' B" + '"' + "'TITLE='B" + '"' + "'>";
htmldef 'C"' as "<IMG SRC='_bnj_ccPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' C" + '"' + "'TITLE='C" + '"' + "'>";
htmldef 'D"' as "<IMG SRC='_bnj_cdPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' D" + '"' + "'TITLE='D" + '"' + "'>";
htmldef 'E"' as "<IMG SRC='_bnj_cePrimePrime.gif' WIDTH=20 HEIGHT=19 " +
      " ALT=' E" + '"' + "'TITLE='E" + '"' + "'>";
htmldef 'F"' as "<IMG SRC='_bnj_cfPrimePrime.gif' WIDTH=20 HEIGHT=19 " +
      " ALT=' F" + '"' + "'TITLE='F" + '"' + "'>";
htmldef 'G"' as "<IMG SRC='_bnj_cgPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' G" + '"' + "'TITLE='G" + '"' + "'>";
htmldef 'H"' as "<IMG SRC='_bnj_chPrimePrime.gif' WIDTH=21 HEIGHT=19 " +
      " ALT=' H" + '"' + "'TITLE='H" + '"' + "'>";
htmldef 'I"' as "<IMG SRC='_bnj_ciPrimePrime.gif' WIDTH=15 HEIGHT=19 " +
      " ALT=' I" + '"' + "'TITLE='I" + '"' + "'>";
htmldef 'J"' as "<IMG SRC='_bnj_cjPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' J" + '"' + "'TITLE='J" + '"' + "'>";
htmldef 'K"' as "<IMG SRC='_bnj_ckPrimePrime.gif' WIDTH=21 HEIGHT=19 " +
      " ALT=' K" + '"' + "'TITLE='K" + '"' + "'>";
htmldef 'L"' as "<IMG SRC='_bnj_clPrimePrime.gif' WIDTH=17 HEIGHT=19 " +
      " ALT=' L" + '"' + "'TITLE='L" + '"' + "'>";
htmldef 'M"' as "<IMG SRC='_bnj_cmPrimePrime.gif' WIDTH=22 HEIGHT=19 " +
      " ALT=' M" + '"' + "'TITLE='M" + '"' + "'>";
htmldef 'N"' as "<IMG SRC='_bnj_cnPrimePrime.gif' WIDTH=21 HEIGHT=19 " +
      " ALT=' N" + '"' + "'TITLE='N" + '"' + "'>";
htmldef 'O"' as "<IMG SRC='_bnj_coPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' O" + '"' + "'TITLE='O" + '"' + "'>";
htmldef 'P"' as "<IMG SRC='_bnj_cpPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' P" + '"' + "'TITLE='P" + '"' + "'>";
htmldef 'Q"' as "<IMG SRC='_bnj_cqPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' Q" + '"' + "'TITLE='Q" + '"' + "'>";
htmldef 'R"' as "<IMG SRC='_bnj_crPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' R" + '"' + "'TITLE='R" + '"' + "'>";
htmldef 'S"' as "<IMG SRC='_bnj_csPrimePrime.gif' WIDTH=18 HEIGHT=19 " +
      " ALT=' S" + '"' + "'TITLE='S" + '"' + "'>";
htmldef 'T"' as "<IMG SRC='_bnj_ctPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' T" + '"' + "'TITLE='T" + '"' + "'>";
htmldef 'U"' as "<IMG SRC='_bnj_cuPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' U" + '"' + "'TITLE='U" + '"' + "'>";
htmldef 'V"' as "<IMG SRC='_bnj_cvPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' V" + '"' + "'TITLE='V" + '"' + "'>";
htmldef 'W"' as "<IMG SRC='_bnj_cwPrimePrime.gif' WIDTH=23 HEIGHT=19 " +
      " ALT=' W" + '"' + "'TITLE='W" + '"' + "'>";
htmldef 'X"' as "<IMG SRC='_bnj_cxPrimePrime.gif' WIDTH=20 HEIGHT=19 " +
      " ALT=' X" + '"' + "'TITLE='X" + '"' + "'>";
htmldef 'Y"' as "<IMG SRC='_bnj_cyPrimePrime.gif' WIDTH=19 HEIGHT=19 " +
      " ALT=' Y" + '"' + "'TITLE='Y" + '"' + "'>";
htmldef 'Z"' as "<IMG SRC='_bnj_czPrimePrime.gif' WIDTH=18 HEIGHT=19 " +
      " ALT=' Z" + '"' + "'TITLE='Z" + '"' + "'>";
althtmldef 'A"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D434;&Prime;</SPAN>';
althtmldef 'B"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D435;&Prime;</SPAN>';
althtmldef 'C"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D436;&Prime;</SPAN>';
althtmldef 'D"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D437;&Prime;</SPAN>';
althtmldef 'E"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D438;&Prime;</SPAN>';
althtmldef 'F"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;&Prime;</SPAN>';
althtmldef 'G"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43A;&Prime;</SPAN>';
althtmldef 'H"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43B;&Prime;</SPAN>';
althtmldef 'I"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43C;&Prime;</SPAN>';
althtmldef 'J"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43D;&Prime;</SPAN>';
althtmldef 'K"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43E;&Prime;</SPAN>';
althtmldef 'L"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;&Prime;</SPAN>';
althtmldef 'M"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D440;&Prime;</SPAN>';
althtmldef 'N"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D441;&Prime;</SPAN>';
althtmldef 'O"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D442;&Prime;</SPAN>';
althtmldef 'P"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D443;&Prime;</SPAN>';
althtmldef 'Q"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D444;&Prime;</SPAN>';
althtmldef 'R"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D445;&Prime;</SPAN>';
althtmldef 'S"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D446;&Prime;</SPAN>';
althtmldef 'T"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D447;&Prime;</SPAN>';
althtmldef 'U"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D448;&Prime;</SPAN>';
althtmldef 'V"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;&Prime;</SPAN>';
althtmldef 'W"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44A;&Prime;</SPAN>';
althtmldef 'X"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44B;&Prime;</SPAN>';
althtmldef 'Y"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44C;&Prime;</SPAN>';
althtmldef 'Z"' as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44D;&Prime;</SPAN>';
latexdef 'A"' as "A''";
latexdef 'B"' as "B''";
latexdef 'C"' as "C''";
latexdef 'D"' as "D''";
latexdef 'E"' as "E''";
latexdef 'F"' as "F''";
latexdef 'G"' as "G''";
latexdef 'H"' as "H''";
latexdef 'I"' as "I''";
latexdef 'J"' as "J''";
latexdef 'K"' as "K''";
latexdef 'L"' as "L''";
latexdef 'M"' as "M''";
latexdef 'N"' as "N''";
latexdef 'O"' as "O''";
latexdef 'P"' as "P''";
latexdef 'Q"' as "Q''";
latexdef 'R"' as "R''";
latexdef 'S"' as "S''";
latexdef 'T"' as "T''";
latexdef 'U"' as "U''";
latexdef 'V"' as "V''";
latexdef 'W"' as "W''";
latexdef 'X"' as "X''";
latexdef 'Y"' as "Y''";
latexdef 'Z"' as "Z''";
htmldef "A0" as "<IMG SRC='_bnj_ca0.gif' WIDTH=18 HEIGHT=19" +
    " ALT=' A0' TITLE='A0'>";
htmldef "B0" as "<IMG SRC='_bnj_cb0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' B0' TITLE='B0'>";
htmldef "C0" as "<IMG SRC='_bnj_cc0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' C0' TITLE='C0'>";
htmldef "D0" as "<IMG SRC='_bnj_cd0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' D0' TITLE='D0'>";
htmldef "E0" as "<IMG SRC='_bnj_ce0.gif' WIDTH=20 HEIGHT=19" +
    " ALT=' E0' TITLE='E0'>";
htmldef "F0" as "<IMG SRC='_bnj_cf0.gif' WIDTH=20 HEIGHT=19" +
    " ALT=' F0' TITLE='F0'>";
htmldef "G0" as "<IMG SRC='_bnj_cg0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' G0' TITLE='G0'>";
htmldef "H0" as "<IMG SRC='_bnj_ch0.gif' WIDTH=21 HEIGHT=19" +
    " ALT=' H0' TITLE='H0'>";
htmldef "I0" as "<IMG SRC='_bnj_ci0.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' I0' TITLE='I0'>";
htmldef "J0" as "<IMG SRC='_bnj_cj0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' J0' TITLE='J0'>";
htmldef "K0" as "<IMG SRC='_bnj_ck0.gif' WIDTH=21 HEIGHT=19" +
    " ALT=' K0' TITLE='K0'>";
htmldef "L0" as "<IMG SRC='_bnj_cl0.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' L0' TITLE='L0'>";
htmldef "M0" as "<IMG SRC='_bnj_cm0.gif' WIDTH=22 HEIGHT=19" +
    " ALT=' M0' TITLE='M0'>";
htmldef "N0" as "<IMG SRC='_bnj_cn0.gif' WIDTH=21 HEIGHT=19" +
    " ALT=' N0' TITLE='N0'>";
htmldef "O0" as "<IMG SRC='_bnj_co0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' O0' TITLE='O0'>";
htmldef "P0" as "<IMG SRC='_bnj_cp0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' P0' TITLE='P0'>";
htmldef "Q0" as "<IMG SRC='_bnj_cq0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' Q0' TITLE='Q0'>";
htmldef "R0" as "<IMG SRC='_bnj_cr0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' R0' TITLE='R0'>";
htmldef "S0" as "<IMG SRC='_bnj_cs0.gif' WIDTH=18 HEIGHT=19" +
    " ALT=' S0' TITLE='S0'>";
htmldef "T0" as "<IMG SRC='_bnj_ct0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' T0' TITLE='T0'>";
htmldef "U0" as "<IMG SRC='_bnj_cu0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' U0' TITLE='U0'>";
htmldef "V0" as "<IMG SRC='_bnj_cv0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' V0' TITLE='V0'>";
htmldef "W0" as "<IMG SRC='_bnj_cw0.gif' WIDTH=23 HEIGHT=19" +
    " ALT=' W0' TITLE='W0'>";
htmldef "X0" as "<IMG SRC='_bnj_cx0.gif' WIDTH=20 HEIGHT=19" +
    " ALT=' X0' TITLE='X0'>";
htmldef "Y0" as "<IMG SRC='_bnj_cy0.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' Y0' TITLE='Y0'>";
htmldef "Z0" as "<IMG SRC='_bnj_cz0.gif' WIDTH=18 HEIGHT=19" +
    " ALT=' Z0' TITLE='Z0'>";
althtmldef "A0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D434;<SUB>0</SUB></SPAN>';
althtmldef "B0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D435;<SUB>0</SUB></SPAN>';
althtmldef "C0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D436;<SUB>0</SUB></SPAN>';
althtmldef "D0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D437;<SUB>0</SUB></SPAN>';
althtmldef "E0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D438;<SUB>0</SUB></SPAN>';
althtmldef "F0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;<SUB>0</SUB></SPAN>';
althtmldef "G0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43A;<SUB>0</SUB></SPAN>';
althtmldef "H0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43B;<SUB>0</SUB></SPAN>';
althtmldef "I0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43C;<SUB>0</SUB></SPAN>';
althtmldef "J0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43D;<SUB>0</SUB></SPAN>';
althtmldef "K0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43E;<SUB>0</SUB></SPAN>';
althtmldef "L0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;<SUB>0</SUB></SPAN>';
althtmldef "M0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D440;<SUB>0</SUB></SPAN>';
althtmldef "N0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D441;<SUB>0</SUB></SPAN>';
althtmldef "O0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D442;<SUB>0</SUB></SPAN>';
althtmldef "P0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D443;<SUB>0</SUB></SPAN>';
althtmldef "Q0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D444;<SUB>0</SUB></SPAN>';
althtmldef "R0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D445;<SUB>0</SUB></SPAN>';
althtmldef "S0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D446;<SUB>0</SUB></SPAN>';
althtmldef "T0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D447;<SUB>0</SUB></SPAN>';
althtmldef "U0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D448;<SUB>0</SUB></SPAN>';
althtmldef "V0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;<SUB>0</SUB></SPAN>';
althtmldef "W0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44A;<SUB>0</SUB></SPAN>';
althtmldef "X0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44B;<SUB>0</SUB></SPAN>';
althtmldef "Y0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44C;<SUB>0</SUB></SPAN>';
althtmldef "Z0" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44D;<SUB>0</SUB></SPAN>';
latexdef "A0" as "A_0";
latexdef "B0" as "B_0";
latexdef "C0" as "C_0";
latexdef "D0" as "D_0";
latexdef "E0" as "E_0";
latexdef "F0" as "F_0";
latexdef "G0" as "G_0";
latexdef "H0" as "H_0";
latexdef "I0" as "I_0";
latexdef "J0" as "J_0";
latexdef "K0" as "K_0";
latexdef "L0" as "L_0";
latexdef "M0" as "M_0";
latexdef "N0" as "N_0";
latexdef "O0" as "O_0";
latexdef "P0" as "P_0";
latexdef "Q0" as "Q_0";
latexdef "R0" as "R_0";
latexdef "S0" as "S_0";
latexdef "T0" as "T_0";
latexdef "U0" as "U_0";
latexdef "V0" as "V_0";
latexdef "W0" as "W_0";
latexdef "X0" as "X_0";
latexdef "Y0" as "Y_0";
latexdef "Z0" as "Z_0";
htmldef "A1_"  as "<IMG SRC='_bnj_ca1.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' A1' TITLE='A1'>";
htmldef "B1_"  as "<IMG SRC='_bnj_cb1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' B1' TITLE='B1'>";
htmldef "C1_"  as "<IMG SRC='_bnj_cc1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' C1' TITLE='C1'>";
htmldef "D1_"  as "<IMG SRC='_bnj_cd1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' D1' TITLE='D1'>";
htmldef "E1"  as "<IMG SRC='_bnj_ce1.gif' WIDTH=18 HEIGHT=19" +
    " ALT=' E1' TITLE='E1'>";
htmldef "F1_"  as "<IMG SRC='_bnj_cf1.gif' WIDTH=18 HEIGHT=19" +
    " ALT=' F1' TITLE='F1'>";
htmldef "G1_"  as "<IMG SRC='_bnj_cg1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' G1' TITLE='G1'>";
htmldef "H1_"  as "<IMG SRC='_bnj_ch1.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' H1' TITLE='H1'>";
htmldef "I1_"  as "<IMG SRC='_bnj_ci1.gif' WIDTH=13 HEIGHT=19" +
    " ALT=' I1' TITLE='I1'>";
htmldef "J1"  as "<IMG SRC='_bnj_cj1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' J1' TITLE='J1'>";
htmldef "K1"  as "<IMG SRC='_bnj_ck1.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' K1' TITLE='K1'>";
htmldef "L1_"  as "<IMG SRC='_bnj_cl1.gif' WIDTH=15 HEIGHT=19" +
    " ALT=' L1' TITLE='L1'>";
htmldef "M1_"  as "<IMG SRC='_bnj_cm1.gif' WIDTH=20 HEIGHT=19" +
    " ALT=' M1' TITLE='M1'>";
htmldef "N1"  as "<IMG SRC='_bnj_cn1.gif' WIDTH=19 HEIGHT=19" +
    " ALT=' N1' TITLE='N1'>";
htmldef "O1_"  as "<IMG SRC='_bnj_co1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' O1_' TITLE='O1_'>";
htmldef "P1"  as "<IMG SRC='_bnj_cp1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' P1' TITLE='P1'>";
htmldef "Q1"  as "<IMG SRC='_bnj_cq1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' Q1' TITLE='Q1'>";
htmldef "R1_" as "<IMG SRC='_bnj_cr1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' R1_' TITLE='R1_'>";
htmldef "S1_"  as "<IMG SRC='_bnj_cs1.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' S1' TITLE='S1'>";
htmldef "T1"  as "<IMG SRC='_bnj_ct1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' T1' TITLE='T1'>";
htmldef "U1"  as "<IMG SRC='_bnj_cu1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' U1' TITLE='U1'>";
htmldef "V1_"  as "<IMG SRC='_bnj_cv1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' V1' TITLE='V1'>";
htmldef "W1"  as "<IMG SRC='_bnj_cw1.gif' WIDTH=21 HEIGHT=19" +
    " ALT=' W1' TITLE='W1'>";
htmldef "X1"  as "<IMG SRC='_bnj_cx1.gif' WIDTH=18 HEIGHT=19" +
    " ALT=' X1' TITLE='X1'>";
htmldef "Y1"  as "<IMG SRC='_bnj_cy1.gif' WIDTH=17 HEIGHT=19" +
    " ALT=' Y1' TITLE='Y1'>";
htmldef "Z1"  as "<IMG SRC='_bnj_cz1.gif' WIDTH=16 HEIGHT=19" +
    " ALT=' Z1' TITLE='Z1'>";
althtmldef "A1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D434;<SUB>1</SUB></SPAN>';
althtmldef "B1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D435;<SUB>1</SUB></SPAN>';
althtmldef "C1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D436;<SUB>1</SUB></SPAN>';
althtmldef "D1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D437;<SUB>1</SUB></SPAN>';
althtmldef "E1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D438;<SUB>1</SUB></SPAN>';
althtmldef "F1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D439;<SUB>1</SUB></SPAN>';
althtmldef "G1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43A;<SUB>1</SUB></SPAN>';
althtmldef "H1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43B;<SUB>1</SUB></SPAN>';
althtmldef "I1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43C;<SUB>1</SUB></SPAN>';
althtmldef "J1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43D;<SUB>1</SUB></SPAN>';
althtmldef "K1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43E;<SUB>1</SUB></SPAN>';
althtmldef "L1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D43F;<SUB>1</SUB></SPAN>';
althtmldef "M1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D440;<SUB>1</SUB></SPAN>';
althtmldef "N1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D441;<SUB>1</SUB></SPAN>';
althtmldef "O1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D442;<SUB>1</SUB></SPAN>';
althtmldef "P1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D443;<SUB>1</SUB></SPAN>';
althtmldef "Q1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D444;<SUB>1</SUB></SPAN>';
althtmldef "R1_" as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D445;<SUB>1</SUB></SPAN>';
althtmldef "S1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D446;<SUB>1</SUB></SPAN>';
althtmldef "T1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D447;<SUB>1</SUB></SPAN>';
althtmldef "U1"  as
   '<SPAN CLASS=class STYLE="color:#C3C">&#x1D448;<SUB>1</SUB></SPAN>';
althtmldef "V1_"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D449;<SUB>1</SUB></SPAN>';
althtmldef "W1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44A;<SUB>1</SUB></SPAN>';
althtmldef "X1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44B;<SUB>1</SUB></SPAN>';
althtmldef "Y1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44C;<SUB>1</SUB></SPAN>';
althtmldef "Z1"  as
    '<SPAN CLASS=class STYLE="color:#C3C">&#x1D44D;<SUB>1</SUB></SPAN>';
latexdef "A1_"  as "A_1";
latexdef "B1_"  as "B_1";
latexdef "C1_"  as "C_1";
latexdef "D1_"  as "D_1";
latexdef "E1"  as "E_1";
latexdef "F1_"  as "F_1";
latexdef "G1_"  as "G_1";
latexdef "H1_"  as "H_1";
latexdef "I1_"  as "I_1";
latexdef "J1"  as "J_1";
latexdef "K1"  as "K_1";
latexdef "L1_"  as "L_1";
latexdef "M1_"  as "M_1";
latexdef "N1"  as "N_1";
latexdef "O1_"  as "O_1";
latexdef "P1"  as "P_1";
latexdef "Q1"  as "Q_1";
latexdef "R1_" as "R_1";
latexdef "S1_"  as "S_1";
latexdef "T1"  as "T_1";
latexdef "U1"  as "U_1";
latexdef "V1_"  as "V_1";
latexdef "W1"  as "W_1";
latexdef "X1"  as "X_1";
latexdef "Y1"  as "Y_1";
latexdef "Z1"  as "Z_1";
/*
htmldef "_fns" as
    " <IMG SRC='_fns.gif' WIDTH=19 HEIGHT=19 ALT=' fns' TITLE='fns'> ";
  althtmldef "_fns" as " fns ";
  latexdef "_fns" as "\mathrm{fns}";
*/
htmldef "_pred" as
    " <IMG SRC='_pred.gif' WIDTH=30 HEIGHT=19 ALT=' pred' TITLE='pred'>";
  althtmldef "_pred" as " pred";
  latexdef "_pred" as "\mathrm{pred}";
htmldef "_Se" as
    " <IMG SRC='_cse.gif' WIDTH=15 HEIGHT=19 ALT=' Se' TITLE='Se'> ";
  althtmldef "_Se" as " Se ";
  latexdef "_Se" as "\mathrel{\operatorname{Se}}";
htmldef "_FrSe" as
    " <IMG SRC='_frse.gif' WIDTH=30 HEIGHT=19 ALT=' FrSe' TITLE='FrSe'> ";
  althtmldef "_FrSe" as " FrSe ";
  latexdef "_FrSe" as "\mathrel{\operatorname{FrSe}}";
htmldef "_trCl" as
    " <IMG SRC='_trcl.gif' WIDTH=26 HEIGHT=19 ALT=' trCl' TITLE='trCl'>";
  althtmldef "_trCl" as " trCl";
  latexdef "_trCl" as "\mathrm{trCl}";
htmldef "_TrFo" as
    " <IMG SRC='_trfo.gif' WIDTH=32 HEIGHT=19 ALT=' TrFo' TITLE='TrFo'>";
  althtmldef "_TrFo" as " TrFo";
  latexdef "_TrFo" as "\mathrm{TrFo}";
/* End of Jonathan Ben-Naim's mathbox */

/* Mathbox of BJ */
htmldef "Prv" as "Prv ";
  althtmldef "Prv" as "Prv ";
  latexdef "Prv" as "\operatorname{Prv}";
htmldef "E**" as "E**";
  althtmldef "E**" as '&exist;**';
  latexdef "E**" as "\exists^{**}";
htmldef "{{" as "{";
  althtmldef "{{" as "{";
  latexdef "{{" as "\{";
htmldef "}}" as "}";
  althtmldef "}}" as "}";
  latexdef "}}" as "\}";
htmldef "F//" as "F//";
  althtmldef "F//" as "&#8498;'";
  latexdef "F//" as "\Finv'";
htmldef "sngl" as "sngl ";
  althtmldef "sngl" as "sngl ";
  latexdef "sngl" as "\operatorname{sngl}";
htmldef "tag" as "tag ";
  althtmldef "tag" as "tag ";
  latexdef "tag" as "\operatorname{tag}";
htmldef "(|" as "(|";
  althtmldef "(|" as "&#x2985;";
  latexdef "(|" as "\mathopen{(\!|}";
htmldef "|)" as "|)";
  althtmldef "|)" as "&#x2986";
  latexdef "|)" as "\mathclose{|\!)}";
htmldef ",," as ", ";
  althtmldef ",," as ", ";
  latexdef ",," as ", ";
htmldef "Proj" as " Proj ";
  althtmldef "Proj" as " Proj ";
  latexdef "Proj" as "\mathbin{Proj}";
htmldef "pr1" as "pr<sub>1</sub> ";
  althtmldef "pr1" as "pr<sub>1</sub> ";
  latexdef "pr1" as "\operatorname{pr_1}";
htmldef "pr2" as "pr<sub>2</sub> ";
  althtmldef "pr2" as "pr<sub>2</sub> ";
  latexdef "pr2" as "\operatorname{pr_2}";
htmldef "if-" as "if-";
  althtmldef "if-" as "if-";
  latexdef "if-" as "\operatorname{if}";
htmldef "elwise" as "elwise";
  althtmldef "elwise" as "elwise";
  latexdef "elwise" as "\operatorname{elwise}";
htmldef "Moore_" as "Moore_";
  althtmldef "Moore_" as "<u>Moore</u>";
  latexdef "Moore_" as "\underline{\mathrm{Moore}}";
htmldef "-Set->" as " -Set-> ";
  althtmldef "-Set->" as ' <span style = " ' +
    ' overflow: visible; width: 0px; height: 0px; display: inline-block; ' +
    ' font-size: 65%; position: relative; top: -1.4ex; ' +
    ' left: 0.4ex">Set</span>&#x27f6; ';
  latexdef "-Set->" as "\overset{\text{Set}}{\longrightarrow}";
htmldef "-Top->" as " -Top-> ";
  althtmldef "-Top->" as ' <span style = " ' +
    ' overflow: visible; width: 0px; height: 0px; display: inline-block; ' +
    ' font-size: 65%; position: relative; top: -1.4ex; ' +
    ' left: 0.4ex">Top</span>&#x27f6; ';
  latexdef "-Top->" as "\overset{\text{Top}}{\longrightarrow}";
htmldef "-Mgm->" as " -Mgm-> ";
  althtmldef "-Mgm->" as ' <span style = " ' +
    ' overflow: visible; width: 0px; height: 0px; display: inline-block; ' +
    ' font-size: 65%; position: relative; top: -1.4ex; ' +
    ' left: 0.4ex">Mgm</span>&#x27f6; ';
  latexdef "-Mgm->" as "\overset{\text{Mgm}}{\longrightarrow}";
htmldef "-TopMgm->" as " -TopMgm-> ";
  althtmldef "-TopMgm->" as ' <span style = " ' +
    ' overflow: visible; width: 0px; height: 0px; display: inline-block; ' +
    ' font-size: 65%; position: relative; top: -1.4ex; ' +
    ' left: 0.0ex">TopMgm</span>&#x27f6; ';
  latexdef "-TopMgm->" as "\overset{\text{TopMgm}}{\longrightarrow}";
htmldef "curry_" as "curry_";
  althtmldef "curry_" as "curry_";
  latexdef "curry_" as "\operatorname{curry}";
htmldef "uncurry_" as "uncurry_";
  althtmldef "uncurry_" as "uncurry_";
  latexdef "uncurry_" as "\operatorname{uncurry}";
htmldef "[s" as "[";
  althtmldef "[s" as "[";
  latexdef "[s" as "[";
htmldef "]s" as "]s";
  althtmldef "]s" as "]<SUB>struct</SUB>";
  latexdef "]s" as "]_\mathrm{struct}";
htmldef "_Id" as "Id";
  althtmldef "_Id" as "Id";
  latexdef "_Id" as "\operatorname{Id}";
htmldef "~P_*" as "~P_*";
  althtmldef "~P_*" as "&#119979;<sub>*</sub>";
  latexdef "~P_*" as "\mathrel{\mathcal{P}_*}";
htmldef "~P^*" as "~P^*";
  althtmldef "~P^*" as "&#119979;<sup>*</sup>";
  latexdef "~P^*" as "\mathrel{\mathcal{P}^*}";
htmldef "1/2" as "1/2";
  althtmldef "1/2" as "1/2";
  latexdef "1/2" as "1/2";
htmldef "CCinfty" as "CCinfty";
  althtmldef "CCinfty" as "&#8450;<SUB>&infin;</SUB>";
  latexdef "CCinfty" as "\mathbb{C}_\infty";
htmldef "CCinftyN" as "CCinftyN";
  althtmldef "CCinftyN" as "&#8450;<SUB>&infin;N</SUB>";
  latexdef "CCinftyN" as "{\mathbb{C}_\infty}";
htmldef "CCbar" as "CCbar";
  althtmldef "CCbar" as "&#8450;&#x305;";
  latexdef "CCbar" as "\overline{\mathbb{C}}";
htmldef "RRbar" as "RRbar";
  althtmldef "RRbar" as "&#8477;&#x305;";
  latexdef "RRbar" as "\overline{\mathbb{R}}";
htmldef "+cc" as " +cc ";
  althtmldef "+cc" as " +<SUB>&#8450;&#x305;</SUB> ";
  latexdef "+cc" as " +_{\overline{\mathbb{C}}} ";
htmldef "-cc" as "-cc";
  althtmldef "-cc" as "-<SUB>&#8450;&#x305;</SUB>";
  latexdef "-cc" as "-_{\overline{\mathbb{C}}}";
htmldef "<rr" as "<rr";
  althtmldef "<rr" as "&lt;<SUB>&#8477;&#x305;</SUB>";
  latexdef "<rr" as "<_{\overline{\mathbb{R}}}";
htmldef ".cc" as " .cc ";
  althtmldef ".cc" as " &#183;<SUB>&#8450;&#x305;</SUB> ";
  latexdef ".cc" as " \cdot_{\overline{\mathbb{C}}} ";
htmldef "invc" as "invc";
  althtmldef "invc" as "<SUP>-1</SUP><SUB>&#8450;&#x305;</SUB>";
  latexdef "invc" as "\cdot^{-1}";
htmldef "iomnn" as "iomnn";
  althtmldef "iomnn" as "i<SUB>&omega;&hookrightarrow;&#8469;</SUB>";
  latexdef "iomnn" as "i_{\omega \hookrightarrow \overline{\mathbb{N}}}";
htmldef "Arg" as "Arg";
  althtmldef "Arg" as "Arg";
  latexdef "Arg" as "\operatorname{Arg}";
htmldef "RR>=0" as "RR>=0";
  althtmldef "RR>=0" as "&#8477;<SUB>&ge;0</SUB>";
  latexdef "RR>=0" as "\mathbb{R}_{\geq 0}";
htmldef "RR>0" as "RR>0";
  althtmldef "RR>0" as "&#8477;<SUB>>0</SUB>";
  latexdef "RR>0" as "\mathbb{R}_{>0}";
htmldef "{R" as "{R";
  althtmldef "{R" as "{<I><SUB><B>R</B></SUB></I>";
  latexdef "{R" as "\{_R";
htmldef "inftyexpi" as "inftyexpi ";
  althtmldef "inftyexpi" as "+&infin;e<SUP>i</SUP>";
  latexdef "inftyexpi" as "+\infty\mathrm{e^i}";
htmldef "inftyexpitau" as "inftyexpitau ";
  althtmldef "inftyexpitau" as "+&infin;e<SUP>i&tau;</SUP>";
  latexdef "inftyexpitau" as "+\infty\mathrm{e^{i\tau}}";
htmldef "minfty" as "minfty";
  althtmldef "minfty" as "-&infin;";
  latexdef "minfty" as "-\infty";
htmldef "pinfty" as "pinfty";
  althtmldef "pinfty" as "+&infin;";
  latexdef "pinfty" as "+\infty";
htmldef "infty" as "infty";
  althtmldef "infty" as "&infin;";
  latexdef "infty" as "\infty";
htmldef "CChat" as "CChat";
  althtmldef "CChat" as "&#8450;&#x302;";
  latexdef "CChat" as "\hat{\mathbb{C}}";
htmldef "RRhat" as "RRhat";
  althtmldef "RRhat" as "&#8477;&#x302;";
  latexdef "RRhat" as "\hat{\mathbb{R}}";
htmldef "NNbar" as "NNbar";
  althtmldef "NNbar" as "&#8469;&#x305;";
  latexdef "NNbar" as "\bar{\mathbb{N}}";
htmldef "ZZbar" as "ZZbar";
  althtmldef "ZZbar" as "&#8484;&#x305;";
  latexdef "ZZbar" as "\bar{\mathbb{Z}}";
htmldef "ZZhat" as "ZZhat";
  althtmldef "ZZhat" as "&#8484;&#x302;";
  latexdef "ZZhat" as "\hat{\mathbb{Z}}";
htmldef "||C" as " ||C ";
  althtmldef "||C" as " &#8741;<sub>&#8450;</sub> ";
  latexdef "||C" as "\mathrel{\parallel_{\mathbb{C}}}";
htmldef "FinSum" as " FinSum ";
  althtmldef "FinSum" as " FinSum ";
  latexdef "FinSum" as " \mathrm{FinSum} ";
htmldef "RRVec" as "RR-Vec";
  althtmldef "RRVec" as "&#8477;-Vec";
  latexdef "RRVec" as "{\mathbb{R}-\mathrm{Vec}}";
htmldef "End" as "End ";
  althtmldef "End" as "End ";
  latexdef "End" as "\operatorname{End}";
/* End of BJ's mathbox */

/* Mathbox of Norm Megill */
htmldef "LSAtoms" as "LSAtoms";
  althtmldef "LSAtoms" as "LSAtoms";
  latexdef "LSAtoms" as "\mathrm{LSAtoms}";
htmldef "LSHyp" as "LSHyp";
  althtmldef "LSHyp" as "LSHyp";
  latexdef "LSHyp" as "\mathrm{LSHyp}";
htmldef "<oL" as
    " <IMG SRC='lessdot.gif' WIDTH=11 HEIGHT=19 "
    + "ALT=' &lt;oL' TITLE='&lt;oL'><SUB>L</SUB> ";
  althtmldef "<oL" as ' &#8918;<SUB>L</SUB> ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "<oL" as "\lessdot_\mathrm{L}";
htmldef "LFnl" as "LFnl";
  althtmldef "LFnl" as "LFnl";
  latexdef "LFnl" as "\mathrm{LFnl}";
htmldef "LKer" as "LKer";
  althtmldef "LKer" as "LKer";
  latexdef "LKer" as "\mathrm{LKer}";
htmldef "LDual" as "LDual";
  althtmldef "LDual" as "LDual";
  latexdef "LDual" as "\mathrm{LDual}";
htmldef "OP" as "<IMG SRC='_op.gif' WIDTH=20 HEIGHT=19 ALT=' OP' TITLE='OP'>";
  althtmldef "OP" as "OP";
  latexdef "OP" as "\mathrm{OP}";
htmldef "cm" as
    "<IMG SRC='_rmcm.gif' WIDTH=19 HEIGHT=19 ALT=' cm' TITLE='cm'>";
  althtmldef "cm" as "cm";
  latexdef "cm" as "\mathrm{cm}";
htmldef "OL" as "<IMG SRC='_ol.gif' WIDTH=20 HEIGHT=19 ALT=' OL' TITLE='OL'>";
  althtmldef "OL" as "OL";
  latexdef "OL" as "\mathrm{OL}";
htmldef "OML" as
    "<IMG SRC='_oml.gif' WIDTH=32 HEIGHT=19 ALT=' OML' TITLE='OML'>";
  althtmldef "OML" as "OML";
  latexdef "OML" as "\mathrm{OML}";
htmldef "<o" as
    " <IMG SRC='lessdot.gif' WIDTH=11 HEIGHT=19 "
    + "ALT=' &lt;o' TITLE='&lt;o'> ";
  althtmldef "<o" as ' &#8918; ';
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "<o" as '\lessdot';
htmldef "Atoms" as
    "<IMG SRC='_atoms.gif' WIDTH=41 HEIGHT=19 ALT=' Atoms' TITLE='Atoms'>";
  althtmldef "Atoms" as "Atoms";
  latexdef "Atoms" as "\mathrm{Atoms}";
htmldef "AtLat" as
    "<IMG SRC='_atlat.gif' WIDTH=39 HEIGHT=19 ALT=' AtLat' TITLE='AtLat'>";
  althtmldef "AtLat" as "AtLat";
  latexdef "AtLat" as "\mathrm{AtLat}";
/*
htmldef "AtsLat" as "AtsLat";
  althtmldef "AtsLat" as "AtsLat";
*/
htmldef "CvLat" as
    "<IMG SRC='_cvlat.gif' WIDTH=41 HEIGHT=19 ALT=' CvLat' TITLE='CvLat'>";
  althtmldef "CvLat" as "CvLat";
  latexdef "CvLat" as "\mathrm{CvLat}";
htmldef "HL" as "<IMG SRC='_hl.gif' WIDTH=19 HEIGHT=19 ALT=' HL' TITLE='HL'>";
  althtmldef "HL" as "HL";
  latexdef "HL" as "\mathrm{HL}";
/*
htmldef "ser" as "ser";
  althtmldef "ser" as "ser";
  latexdef "ser" as "\mathrm{ser}";
htmldef "fcard" as "fcard";
  althtmldef "fcard" as "fcard";
htmldef "idsumf" as "idsumf";
  althtmldef "idsumf" as "idsumf";
htmldef "idsum" as "idsum";
  althtmldef "idsum" as "idsum";
htmldef "C_rng" as "C_rng";
  althtmldef "C_rng" as "C_rng";
htmldef "-vNEW" as "-vNEW";
  althtmldef "-vNEW" as "-vNEW";
htmldef "RVecNEW" as "RVecNEW";
  althtmldef "RVecNEW" as "RVecNEW";
htmldef "+ss" as
    "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>" +
    "<IMG SRC='_subss.gif' WIDTH=10 HEIGHT=19 ALT='ss' TITLE='ss'>";
  althtmldef "+ss" as "+<SUB>ss</SUB>";
  latexdef "+ss" as "+_\mathrm{ss}";
htmldef "SubSpNEW" as "SubSpNEW";
  althtmldef "SubSpNEW" as "SubSpNEW";
htmldef "spanNEW" as "spanNEW";
  althtmldef "spanNEW" as "spanNEW";
htmldef "o+" as "o+";
  althtmldef "o+" as "o+";
htmldef "Ev" as "Ev";
  althtmldef "Ev" as "Ev";
htmldef "/v" as "/v";
  althtmldef "/v" as "/v";
htmldef "normv" as "normv";
  althtmldef "normv" as "normv";
*/
htmldef "LLines" as
    "<IMG SRC='_llines.gif' WIDTH=43 HEIGHT=19 ALT=' LLines' TITLE='LLines'>";
  althtmldef "LLines" as "LLines";
  latexdef "LLines" as "\mathrm{LLines}";
htmldef "LPlanes" as
  "<IMG SRC='_lplanes.gif' WIDTH=51 HEIGHT=19 ALT=' LPlanes' TITLE='LPlanes'>";
  althtmldef "LPlanes" as "LPlanes";
  latexdef "LPlanes" as "\mathrm{LPlanes}";
htmldef "LVols" as
    "<IMG SRC='_lvols.gif' WIDTH=36 HEIGHT=19 ALT=' LVols' TITLE='LVols'>";
  althtmldef "LVols" as "LVols";
  latexdef "LVols" as "\mathrm{LVols}";
htmldef "Lines" as
    "<IMG SRC='_lines.gif' WIDTH=34 HEIGHT=19 ALT=' Lines' TITLE='Lines'>";
  althtmldef "Lines" as "Lines";
  latexdef "Lines" as "\mathrm{Lines}";
htmldef "Points" as
    "<IMG SRC='_points.gif' WIDTH=40 HEIGHT=19 ALT=' Points' TITLE='Points'>";
  althtmldef "Points" as "Points";
  latexdef "Points" as "\mathrm{Points}";
htmldef "PSubSp" as
    "<IMG SRC='_psubsp.gif' WIDTH=49 HEIGHT=19 ALT=' PSubSp' TITLE='PSubSp'>";
  althtmldef "PSubSp" as "PSubSp";
  latexdef "PSubSp" as "\mathrm{PSubSp}";
htmldef "pmap" as
    "<IMG SRC='_pmap.gif' WIDTH=36 HEIGHT=19 ALT=' pmap' TITLE='pmap'>";
  althtmldef "pmap" as "pmap";
  latexdef "pmap" as "\mathrm{pmap}";
htmldef "+P" as
    "<IMG SRC='plus.gif' WIDTH=13 HEIGHT=19 ALT=' +' TITLE='+'>" +
    "<IMG SRC='subcp.gif' WIDTH=8 HEIGHT=19 ALT='P' TITLE='P'>";
  althtmldef "+P" as "+<SUB>&#x1D443;</SUB>";
  latexdef "+P" as "+_P";
htmldef "PCl" as
    "<IMG SRC='_pcl.gif' WIDTH=23 HEIGHT=19 ALT=' PCl' TITLE='PCl'>";
  althtmldef "PCl" as "PCl";
  latexdef "PCl" as "\mathrm{PCl}";
htmldef "_|_P" as
    "<IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 ALT=' _|_' TITLE='_|_'>" +
    "<IMG SRC='subcp.gif' WIDTH=8 HEIGHT=19 ALT='P' TITLE='P'>";
  althtmldef "_|_P" as "&#8869;<SUB>&#x1D443;</SUB>";
    /* 2-Jan-2016 reverted sans-serif */
  latexdef "_|_P" as "\perp_P";
htmldef "PSubCl" as
    "<IMG SRC='_psubcl.gif' WIDTH=47 HEIGHT=19 ALT=' PSubCl' TITLE='PSubCl'>";
  althtmldef "PSubCl" as "PSubCl";
  latexdef "PSubCl" as "\mathrm{PSubCl}";
/*
htmldef "sumP" as "sumP";
  althtmldef "sumP" as "sumP";
htmldef "Indep" as "Indep";
  althtmldef "Indep" as "Indep";
htmldef "BasesP" as "BasesP";
  althtmldef "BasesP" as "BasesP";
htmldef "rankP" as "rankP";
  althtmldef "rankP" as "rankP";
htmldef "PHyp" as "PHyp";
  althtmldef "PHyp" as "PHyp";
htmldef "ww" as "ww";
  althtmldef "ww" as "ww";
*/
htmldef "LHyp" as
    "<IMG SRC='_lhyp.gif' WIDTH=35 HEIGHT=19 ALT=' LHyp' TITLE='LHyp'>";
  althtmldef "LHyp" as "LHyp";
  latexdef "LHyp" as "\mathrm{LHyp}";
htmldef "LAut" as
    "<IMG SRC='_laut.gif' WIDTH=33 HEIGHT=19 ALT=' LAut' TITLE='LAut'>";
  althtmldef "LAut" as "LAut";
  latexdef "LAut" as "\mathrm{LAut}";
htmldef "WAtoms" as
    "<IMG SRC='_watoms.gif' WIDTH=53 HEIGHT=19 ALT=' WAtoms' TITLE='WAtoms'>";
  althtmldef "WAtoms" as "WAtoms";
  latexdef "WAtoms" as "\mathrm{WAtoms}";
htmldef "PAut" as
    "<IMG SRC='_paut.gif' WIDTH=30 HEIGHT=19 ALT=' PAut' TITLE='PAut'>";
  althtmldef "PAut" as "PAut";
  latexdef "PAut" as "\mathrm{PAut}";
htmldef "LDil" as
    "<IMG SRC='_ldil.gif' WIDTH=27 HEIGHT=19 ALT=' LDil' TITLE='LDil'>";
  althtmldef "LDil" as "LDil";
  latexdef "LDil" as "\mathrm{LDil}";
htmldef "LTrn" as
    "<IMG SRC='_ltrn.gif' WIDTH=33 HEIGHT=19 ALT=' LTrn' TITLE='LTrn'>";
  althtmldef "LTrn" as "LTrn";
  latexdef "LTrn" as "\mathrm{LTrn}";
htmldef "Dil" as
    "<IMG SRC='_dil.gif' WIDTH=18 HEIGHT=19 ALT=' Dil' TITLE='Dil'>";
  althtmldef "Dil" as "Dil";
  latexdef "Dil" as "\mathrm{Dil}";
htmldef "Trn" as
    "<IMG SRC='_trn.gif' WIDTH=23 HEIGHT=19 ALT=' Trn' TITLE='Trn'>";
  althtmldef "Trn" as "Trn";
  latexdef "Trn" as "\mathrm{Trn}";
/*
htmldef "trP" as "trP";
  althtmldef "trP" as "trP";
*/
htmldef "trL" as
    "<IMG SRC='_trl.gif' WIDTH=21 HEIGHT=19 ALT=' trL' TITLE='trL'>";
  althtmldef "trL" as "trL";
  latexdef "trL" as "\mathrm{trL}";
htmldef "TGrp" as
    "<IMG SRC='_tgrp.gif' WIDTH=35 HEIGHT=19 ALT=' TGrp' TITLE='TGrp'>";
  althtmldef "TGrp" as "TGrp";
  latexdef "TGrp" as "\mathrm{TGrp}";
htmldef "TEndo" as
    "<IMG SRC='_tendo.gif' WIDTH=42 HEIGHT=19 ALT=' TEndo' TITLE='TEndo'>";
  althtmldef "TEndo" as "TEndo";
  latexdef "TEndo" as "\mathrm{TEndo}";
htmldef "EDRing" as
    "<IMG SRC='_edring.gif' WIDTH=49 HEIGHT=19 ALT=' EDRing' TITLE='EDRing'>";
  althtmldef "EDRing" as "EDRing";
  latexdef "EDRing" as "\mathrm{EDRing}";
htmldef "EDRingR" as
    "<IMG SRC='_edring.gif' WIDTH=49 HEIGHT=19 ALT=' EDRing' TITLE='EDRing'>" +
    "<IMG SRC='subcr.gif' WIDTH=9 HEIGHT=19 ALT='R' TITLE='R'>";
  althtmldef "EDRingR" as "EDRing<SUB>R</SUB>";
  latexdef "EDRingR" as "\mathrm{EDRing}_R";
htmldef "DVecA" as
    "<IMG SRC='_dveca.gif' WIDTH=44 HEIGHT=19 ALT=' DVecA' TITLE='DVecA'>";
  althtmldef "DVecA" as "DVecA";
  latexdef "DVecA" as "\mathrm{DVecA}";
htmldef "DIsoA" as
    "<IMG SRC='_disoa.gif' WIDTH=37 HEIGHT=19 ALT=' DIsoA' TITLE='DIsoA'>";
  althtmldef "DIsoA" as "DIsoA";
  latexdef "DIsoA" as "\mathrm{DIsoA}";
htmldef "DVecH" as
    "<IMG SRC='_dvech.gif' WIDTH=44 HEIGHT=19 ALT=' DVecH' TITLE='DVecH'>";
  althtmldef "DVecH" as "DVecH";
  latexdef "DVecH" as "\mathrm{DVecH}";
htmldef "ocA" as
    "<IMG SRC='_oca.gif' WIDTH=24 HEIGHT=19 ALT=' ocA' TITLE='ocA'>";
  althtmldef "ocA" as "ocA";
  latexdef "ocA" as "\mathrm{ocA}";
htmldef "vA" as "<IMG SRC='_va.gif' WIDTH=16 HEIGHT=19 ALT=' vA' TITLE='vA'>";
  althtmldef "vA" as "vA";
  latexdef "vA" as "\mathrm{vA}";
htmldef "DIsoB" as
    "<IMG SRC='_disob.gif' WIDTH=36 HEIGHT=19 ALT=' DIsoB' TITLE='DIsoB'>";
  althtmldef "DIsoB" as "DIsoB";
  latexdef "DIsoB" as "\mathrm{DIsoB}";
htmldef "DIsoC" as
    "<IMG SRC='_disoc.gif' WIDTH=37 HEIGHT=19 ALT=' DIsoC' TITLE='DIsoC'>";
  althtmldef "DIsoC" as "DIsoC";
  latexdef "DIsoC" as "\mathrm{DIsoC}";
htmldef "DIsoH" as
    "<IMG SRC='_disoh.gif' WIDTH=37 HEIGHT=19 ALT=' DIsoH' TITLE='DIsoH'>";
  althtmldef "DIsoH" as "DIsoH";
  latexdef "DIsoH" as "\mathrm{DIsoH}";
htmldef "ocH" as
    "<IMG SRC='_och.gif' WIDTH=24 HEIGHT=19 ALT=' ocH' TITLE='ocH'>";
  althtmldef "ocH" as "ocH";
  latexdef "ocH" as "\mathrm{ocH}";
htmldef "joinH" as "joinH";
  althtmldef "joinH" as "joinH";
  latexdef "joinH" as "\mathrm{joinH}";
htmldef "LPol" as "LPol";
  althtmldef "LPol" as "LPol";
  latexdef "LPol" as "\mathrm{LPol}";
htmldef "LCDual" as "LCDual";
  althtmldef "LCDual" as "LCDual";
  latexdef "LCDual" as "\mathrm{LCDual}";
htmldef "mapd" as "mapd";
  althtmldef "mapd" as "mapd";
  latexdef "mapd" as "\mathrm{mapd}";
htmldef "HVMap" as "HVMap";
  althtmldef "HVMap" as "HVMap";
  latexdef "HVMap" as "\mathrm{HVMap}";
/*
htmldef "eImage" as "eImage";
  althtmldef "eImage" as "eImage";
  latexdef "eImage" as "\mathrm{eImage}";
*/
htmldef "HDMap1" as "HDMap1";
  althtmldef "HDMap1" as "HDMap1";
  latexdef "HDMap1" as "\mathrm{HDMap1}";
htmldef "HDMap" as "HDMap";
  althtmldef "HDMap" as "HDMap";
  latexdef "HDMap" as "\mathrm{HDMap}";
htmldef "HGMap" as "HGMap";
  althtmldef "HGMap" as "HGMap";
  latexdef "HGMap" as "\mathrm{HGMap}";
htmldef "HLHil" as "HLHil";
  althtmldef "HLHil" as "HLHil";
  latexdef "HLHil" as "\mathrm{HLHil}";
/*
htmldef "*HRing" as "*HRing";
  althtmldef "*HRing" as "*HRing";
  latexdef "*HRing" as "\ast\mathrm{HRing}";
htmldef "hmap" as "hmap";
  althtmldef "hmap" as "hmap";
  latexdef "hmap" as "\mathrm{hmap}";
htmldef "gmap" as "gmap";
  althtmldef "gmap" as "gmap";
  latexdef "gmap" as "\mathrm{gmap}";
htmldef "mapd" as "mapd";
  althtmldef "mapd" as "mapd";
  latexdef "mapd" as "\mathrm{mapd}";
htmldef "GrpEndo" as "GrpEndo";
  althtmldef "GrpEndo" as "GrpEndo";
htmldef "DVecAEndo" as "DVecAEndo";
  althtmldef "DVecAEndo" as "DVecAEndo";
htmldef "ERing" as "ERing";
  althtmldef "ERing" as "ERing";
htmldef "TPEndo" as "TPEndo";
  althtmldef "TPEndo" as "TPEndo";
htmldef "DRing" as "DRing";
  althtmldef "DRing" as "DRing";
htmldef "DVecA" as "DVecA";
  althtmldef "DVecA" as "DVecA";
htmldef "DVIsoPre" as "DVIsoPre";
  althtmldef "DVIsoPre" as "DVIsoPre";
htmldef "DVecB" as "DVecB";
  althtmldef "DVecB" as "DVecB";
htmldef "DVecH" as "DVecH";
  althtmldef "DVecH" as "DVecH";
htmldef "ee" as "ee";
  althtmldef "ee" as "ee";
htmldef "DVIsoA" as "DVIsoA";
  althtmldef "DVIsoA" as "DVIsoA";
htmldef "qtr" as "qtr";
  althtmldef "qtr" as "qtr";
htmldef "DVIsoB" as "DVIsoB";
  althtmldef "DVIsoB" as "DVIsoB";
htmldef "DVIsoC" as "DVIsoC";
  althtmldef "DVIsoC" as "DVIsoC";
htmldef "DVIsoH" as "DVIsoH";
  althtmldef "DVIsoH" as "DVIsoH";
htmldef "S_|_" as "S_|_";
  althtmldef "S_|_" as "S_|_";
htmldef "Ropp" as "Ropp";
  althtmldef "Ropp" as "Ropp";
htmldef "Vldual" as "Vldual";
  althtmldef "Vldual" as "Vldual";
htmldef "vecdom" as "vecdom";
  althtmldef "vecdom" as "vecdom";
htmldef "ker" as "ker";
  althtmldef "ker" as "ker";
htmldef "mapd" as "mapd";
  althtmldef "mapd" as "mapd";
htmldef "eimage" as "eimage";
  althtmldef "eimage" as "eimage";
htmldef "hmap" as "hmap";
  althtmldef "hmap" as "hmap";
htmldef "gmap" as "gmap";
  althtmldef "gmap" as "gmap";
htmldef "HLtoHil" as "HLtoHil";
  althtmldef "HLtoHil" as "HLtoHil";
*/
/* End of Norm Megill's mathbox */

/* Mathbox of Richard Penner */
htmldef "r*" as "<IMG SRC='r.gif' WIDTH=7 HEIGHT=19 ALT=' r' TITLE='r'>" +
    "<IMG SRC='ast.gif' WIDTH=7 HEIGHT=19 ALT='*' TITLE='*'>";
  althtmldef "r*" as "r*";
  latexdef "r*" as "\mathrm{r}*";
htmldef "hereditary" as " hereditary ";
  althtmldef "hereditary" as " hereditary ";
  latexdef "hereditary" as "\mathrm{hereditary}";
/* End of Richard Penner's mathbox */

/* Mathbox of Eric Schmidt */
htmldef "RelPres" as " RelPres ";
  althtmldef "RelPres" as " RelPres ";
  latexdef "RelPres" as "\mathrm{RelPres}";
/* End of Eric Schmidt's mathbox */

/* Mathbox of Glauco Siliprandi */
htmldef "SAlg" as "SAlg";
  althtmldef "SAlg" as "SAlg";
  latexdef "SAlg" as "\mathrm{SAlg}";
htmldef "SalOn" as "SalOn";
  althtmldef "SalOn" as "SalOn";
  latexdef "SalOn" as "\mathrm{SalOn}";
htmldef "SalGen" as "SalGen";
  althtmldef "SalGen" as "SalGen";
  latexdef "SalGen" as "\mathrm{SalGen}";
htmldef "sum^" as "&Sigma;<SUP><small>^</small></SUP>";
  althtmldef "sum^" as "&Sigma;<SUP><small>^</small></SUP>";
  latexdef "sum^" as "\sum\hat{\;}";
htmldef "Meas" as "Meas";
  althtmldef "Meas" as "Meas";
  latexdef "Meas" as "\mathrm{Meas}";
htmldef "OutMeas" as "OutMeas";
  althtmldef "OutMeas" as "OutMeas";
  latexdef "OutMeas" as "\mathrm{OutMeas}";
htmldef "CaraGen" as "CaraGen";
  althtmldef "CaraGen" as "CaraGen";
  latexdef "CaraGen" as "\mathrm{CaraGen}";
htmldef "voln*" as "voln<SUP><small>*</small></SUP>";
  althtmldef "voln*" as "voln*";
  latexdef "voln*" as "\operatorname{voln}^*";
htmldef "voln" as "voln";
  althtmldef "voln" as "voln";
  latexdef "voln" as "\mathrm{voln}";
htmldef "SMblFn" as "SMblFn";
  althtmldef "SMblFn" as "SMblFn";
  latexdef "SMblFn" as "\mathrm{SMblFn}";
htmldef "liminf" as "liminf";
  althtmldef "liminf" as 'lim inf';
  latexdef "liminf" as "\liminf";
htmldef "~~>*" as "~~&gt;*";
  althtmldef "~~>*" as "~~>*";
  latexdef "~~>*" as "\rightsquigarrow *";
/* End of Glauco Siliprandi's mathbox */

/* End of typesetting definition section */
$)
$( End $[ set-typeset.mm $] $)


$( Begin $[ set-hilsp.mm $] $)
$(
