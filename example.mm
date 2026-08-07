$( --- Declare logical constants --- $)
$c wff |- -> -. ( ) $.

$( --- Declare propositional variables --- $)
$v A B C $.

$( --- Type each variable as a well-formed formula --- $)
wA $f wff A $.
wB $f wff B $.
wC $f wff C $.

$( A propositional variable is wff $)
wn $a wff -. A $.
wi $a wff ( A -> B ) $.

$( Axioms $)
ax-1 $a |- ( A -> ( B -> A ) ) $.
ax-2 $a |- ( ( A -> ( B -> C ) ) -> ( ( A -> B ) -> ( A -> C ) ) ) $.
ax-3 $a |- ( ( ( -. B ) -> ( -. A ) ) -> ( ( ( -. B ) -> A ) -> B ) ) $.

$( Modus Ponens: from A and (A->B) conclude B $)
${
  ax-mp.1 $e |- A $.
  ax-mp.2 $e |- ( A -> B ) $.
  ax-mp   $a |- B $.
$}


$( Proof that every wff implies itself $)
id $p |- ( A -> A ) $=
    wA wA wA wi wi                $( wff ( A -> ( A -> A ) )                      -- ax-mp outer: wA $)
    wA wA wi                      $( wff ( A -> A )                               -- ax-mp outer: wB $)
    wA wA ax-1                    $( |- ( A -> ( A -> A ) )                       -- ax-mp outer: premise $)
    wA wA wA wi wA wi wi          $( wff ( A -> ( ( A -> A ) -> A ) )             -- ax-mp inner: wA $)
    wA wA wA wi wi wA wA wi wi    $( wff ( ( A -> ( A -> A ) ) -> ( A -> A ) )    -- ax-mp inner: wB $)
    wA wA wA wi ax-1              $( |- ( A -> ( ( A -> A ) -> A ) )              -- ax-mp inner: premise $)
    wA wA wA wi wA ax-2           $( |- ( ( A -> ( ( A -> A ) -> A ) ) -> ... )   -- ax-mp inner: implication $)
    ax-mp                         $( |- ( ( A -> ( A -> A ) ) -> ( A -> A ) ) $)
    ax-mp                         $( |- ( A -> A ) $)
$.
