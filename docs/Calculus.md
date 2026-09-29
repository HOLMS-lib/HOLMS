# Il calcolo assiomatico modale di HOLMS

Questo capitolo descrive la teoria matematica formalizzata in `calculus.ml` e
in `Calculus.lean`. L'esposizione è indipendente dal linguaggio del verificatore
e dai dettagli delle dimostrazioni formali.

## 1. Scopo del calcolo

Il file definisce un calcolo hilbertiano per la logica modale proposizionale
classica. La base modale è la logica normale **K**, ma il sistema è
parametrizzato da un insieme arbitrario di assiomi aggiuntivi. La stessa
nozione di derivabilità può quindi essere usata per K, GL e altri sistemi
modali normali.

La relazione fondamentale si scrive qui

$$
S;H \vdash p, 
$$

dove:

- $S$ è l'insieme degli assiomi aggiuntivi che determina il sistema modale;
- $H$ è l'insieme delle ipotesi locali;
- $p$ è la formula conclusiva.

La distinzione tra $S$ e $H$ è essenziale. Gli elementi di $S$ si
comportano come assiomi globali del sistema, mentre gli elementi di $H$ sono
assunzioni locali soggette al lemma di deduzione. In particolare, la regola di
necessitazione non permette di trasformare in una necessità una conclusione
che dipenda da ipotesi locali.

Benché il commento iniziale del sorgente faccia riferimento alla logica di
provabilità GL, l'assioma caratteristico di GL non appartiene alla base
primitiva descritta qui. GL si ottiene scegliendo come assiomi aggiuntivi le
istanze appropriate dell'assioma di Löb.

## 2. Linguaggio delle formule

Le formule sono costruite a partire da:

- falsità $\bot$ e verità $\top$;
- variabili proposizionali;
- negazione $\neg p$;
- congiunzione $p\land q$;
- disgiunzione $p\lor q$;
- implicazione $p\to q$;
- equivalenza $p\leftrightarrow q$;
- necessità $\Box p$.

La possibilità è definita per dualità:

$$
\Diamond p := \neg\Box\neg p.
$$

Tutti i connettivi proposizionali fanno parte del linguaggio, ma il calcolo
contiene assiomi che ne fissano il comportamento classico in termini
dell'implicazione e della falsità.

## 3. Base assiomatica

Ogni istanza dei seguenti schemi è un assioma del calcolo.

### 3.1 Implicazione classica

I primi tre schemi costituiscono una base completa per il frammento
implicativo classico con falsità:

$$
p\to(q\to p),
$$

$$
(p\to(q\to r))\to((p\to q)\to(p\to r)),
$$

$$
((p\to\bot)\to\bot)\to p.
$$

Il terzo schema esprime l'eliminazione classica della doppia negazione. Il
calcolo non è quindi intuizionista.

### 3.2 Equivalenza

L'equivalenza è regolata dai tre schemi

$$
(p\leftrightarrow q)\to(p\to q),
$$

$$
(p\leftrightarrow q)\to(q\to p),
$$

$$
(p\to q)\to((q\to p)\to(p\leftrightarrow q)).
$$

Di conseguenza, due formule sono equivalenti esattamente quando sono
derivabili entrambe le implicazioni fra di esse.

### 3.3 Costanti e connettivi proposizionali

Il comportamento dei connettivi rimanenti è fissato da:

$$
\top\leftrightarrow(\bot\to\bot),
$$

$$
\neg p\leftrightarrow(p\to\bot),
$$

$$
p\land q\leftrightarrow((p\to(q\to\bot))\to\bot),
$$

$$
p\lor q\leftrightarrow\neg(\neg p\land\neg q).
$$

Questi schemi rendono esplicito che la logica proposizionale sottostante è
classica e che, dal punto di vista deduttivo, tutti i connettivi possono essere
ricondotti all'implicazione e alla falsità.

### 3.4 Assioma modale K

La normalità dell'operatore di necessità è espressa dallo schema

$$
\Box(p\to q)\to(\Box p\to\Box q).
$$

Esso afferma che la necessità distribuisce sull'implicazione.

## 4. Regole di derivazione

La relazione $S;H\vdash p$ è la più piccola relazione chiusa rispetto alle
regole seguenti.

1. Ogni istanza di uno schema della base K è derivabile.
2. Ogni formula appartenente a $S$ è derivabile.
3. Ogni formula appartenente a $H$ è derivabile.
4. **Modus ponens:** da $S;H\vdash p\to q$ e $S;H\vdash p$ segue
   $S;H\vdash q$.
5. **Necessitazione:** se $S;\varnothing\vdash p$, allora
   $S;H\vdash\Box p$, per qualunque $H$.

La premessa vuota nella necessitazione garantisce che si possano necessitare
soltanto teoremi, cioè formule che non dipendono da assunzioni locali. Gli
assiomi globali in $S$, invece, rimangono disponibili.

## 5. Proprietà strutturali

La derivabilità è monotona in entrambi i suoi parametri insiemistici:

- se $S\subseteq S'$ e $S;H\vdash p$, allora $S';H\vdash p$;
- se $H\subseteq H'$ e $S;H\vdash p$, allora $S;H'\vdash p$.

Aggiungere assiomi o ipotesi non distrugge quindi una derivazione esistente.

Il principale risultato strutturale è il **lemma di deduzione**:

$$
S;H\vdash p\to q
\quad\Longleftrightarrow\quad
S;H\cup\{p\}\vdash q.
$$

Il lemma permette di passare fra implicazioni interne al linguaggio e
ragionamenti condotti sotto un'ipotesi aggiuntiva. La restrizione imposta alla
necessitazione è precisamente ciò che rende valida questa forma del lemma.

Un caso limite importante è l'esplosione del contesto: se
$\bot\in H$, allora $S;H\vdash p$ per ogni formula $p$.

## 6. Calcolo proposizionale derivato

Dalla base primitiva vengono ricostruite le usuali regole della logica
proposizionale classica.

### 6.1 Implicazione

Sono derivabili, fra le altre, le seguenti leggi:

- riflessività: $p\to p$;
- aggiunta di una premessa: da $q$ si ottiene $p\to q$;
- transitività: da $p\to q$ e $q\to r$ si ottiene $p\to r$;
- permutazione delle premesse:
  $(p\to(q\to r))\to(q\to(p\to r))$;
- contrazione: da $p\to(p\to q)$ si ottiene $p\to q$;
- monotonia: da $p'\to p$ e $q\to q'$ si ottiene
  $(p\to q)\to(p'\to q')$.

Queste regole consentono di concatenare e riorganizzare catene di
implicazioni senza alterarne il significato logico.

### 6.2 Falsità, negazione e ragionamento classico

Si dimostrano:

$$
\bot\to p
$$

per ogni $p$, e quindi il principio *ex falso quodlibet*. Sono inoltre
disponibili:

- eliminazione e introduzione della doppia negazione;
- contrapposizione;
- ragionamento per assurdo;
- distinzione dei casi $p$ e $\neg p$;
- terzo escluso $p\lor\neg p$;
- principio di non contraddizione
  $(p\land\neg p)\to\bot$.

In particolare,

$$
\neg\neg p\leftrightarrow p
$$

è un teorema del sistema.

### 6.3 Congiunzione

La congiunzione soddisfa le regole usuali:

- da $p\land q$ si ricavano $p$ e $q$;
- da $p$ e $q$ si ricava $p\land q$;
- un'implicazione con antecedente congiunto può essere trasformata nella
  corrispondente catena di implicazioni, e viceversa.

Sono dimostrate anche commutatività, associatività, identità con $\top$ e
congruenza rispetto all'equivalenza dimostrabile.

### 6.4 Disgiunzione

Per la disgiunzione valgono:

- le due regole di introduzione;
- l'eliminazione per casi;
- commutatività e associatività;
- identità con $\bot$;
- congruenza rispetto all'equivalenza dimostrabile.

L'eliminazione per casi assume la forma

$$
\frac{p\lor q \qquad p\to r \qquad q\to r}{r}.
$$

### 6.5 Equivalenza e sostituzione dei proposizionalmente equivalenti

L'equivalenza dimostrabile è riflessiva, simmetrica e transitiva. Inoltre è
una congruenza per tutti i connettivi proposizionali:

$$
p\leftrightarrow p',\quad q\leftrightarrow q'
$$

permettono di dedurre le equivalenze ottenute sostituendo $p,p'$ e
$q,q'$ dentro negazioni, congiunzioni, disgiunzioni, implicazioni ed
equivalenze.

Questo principio giustifica il ragionamento algebrico sulle formule: una
sottoformula può essere rimpiazzata da una formula dimostrabilmente
equivalente.

### 6.6 Identità booleane

La teoria comprende numerose identità classiche, fra cui:

- le leggi di De Morgan;
- $\neg\top\leftrightarrow\bot$;
- $\neg(p\to q)\leftrightarrow p\land\neg q$;
- caratterizzazioni dell'equivalenza mediante due implicazioni;
- leggi distributive di $\land$ rispetto a $\lor$ e viceversa;
- identità e associatività dei connettivi.

Le versioni formulate come equivalenze interne convivono con regole che
trasportano direttamente la derivabilità da un membro dell'equivalenza
all'altro.

## 7. Conseguenze modali

Dall'assioma K e dalla necessitazione segue la monotonia della necessità sui
teoremi:

$$
S;\varnothing\vdash p\to q
\quad\Longrightarrow\quad
S;H\vdash\Box p\to\Box q.
$$

Di conseguenza, le equivalenze dimostrate senza ipotesi locali possono essere
trasportate sotto $\Box$:

$$
S;\varnothing\vdash p\leftrightarrow q
\quad\Longrightarrow\quad
S;H\vdash\Box p\leftrightarrow\Box q.
$$

La necessità preserva la congiunzione in entrambe le direzioni:

$$
\Box(p\land q)\leftrightarrow(\Box p\land\Box q).
$$

Per la possibilità si ottiene la direzione sempre valida

$$
\Diamond(p\land q)\to(\Diamond p\land\Diamond q).
$$

Il converso non viene affermato: in generale due formule possono essere
possibili in mondi accessibili differenti senza che sia possibile la loro
congiunzione.

## 8. Sostituzione uniforme

Una sostituzione uniforme assegna a ogni variabile proposizionale una formula
e si estende ricorsivamente a tutte le formule. Il calcolo dimostra tre fatti
fondamentali.

1. Gli schemi primitivi di K sono chiusi per sostituzione uniforme.
2. Una derivazione può essere sostituita uniformemente, purché l'insieme
   $S$ degli assiomi aggiuntivi sia chiuso rispetto alla sostituzione scelta.
3. Se due sostituzioni assegnano a ogni variabile formule dimostrabilmente
   equivalenti senza ipotesi locali, allora producono formule
   dimostrabilmente equivalenti in qualunque contesto.

Più precisamente, se $\sigma$ è una sostituzione, $S$ è chiuso rispetto a
$\sigma$, e

$$
S;H\vdash p,
$$

allora

$$
S;\sigma[H]\vdash\sigma(p).
$$

La condizione di chiusura su $S$ è necessaria perché $S$ può essere un
insieme arbitrario di formule, non necessariamente già presentato come schema
chiuso per sostituzione.

## 9. Quadro complessivo

La teoria sviluppata nel file può essere riassunta come segue:

- fornisce una base hilbertiana classica per la logica modale normale K;
- separa assiomi globali e ipotesi locali;
- ricostruisce un'ampia libreria di ragionamento proposizionale;
- dimostra il lemma di deduzione e le proprietà strutturali del giudizio;
- stabilisce le principali regole di congruenza proposizionale e modale;
- garantisce la stabilità del calcolo rispetto alla sostituzione uniforme;
- permette di ottenere sistemi modali specifici scegliendo opportunamente
  l'insieme $S$.

Il risultato è un'infrastruttura sintattica generale sulla quale possono
essere costruite le successive teorie di correttezza, completezza,
decidibilità e costruzione di contromodelli per i singoli sistemi modali.

## 10. Dimostrazioni dei risultati del calcolo

In questa sezione scriviamo semplicemente $\vdash p$ quando gli insiemi
fissi $S$ e $H$ non hanno un ruolo particolare. Ogni uso di una formula
già dimostrata in un contesto più piccolo sottintende la monotonia. Indichiamo
con **MP** il modus ponens e con **DT** il lemma di deduzione.

### 10.1 Regole primitive e monotonia

**Regole `MODPROVES_KAXIOM`, `MODPROVES_AX`, `MODPROVES_HP`,
`MLK_modusponens` e `MLK_necessitation`.** Questi enunciati sono esattamente
le cinque clausole che definiscono la derivabilità: introduzione di un assioma
K, introduzione di un elemento di $S$, introduzione di un'ipotesi, modus
ponens e necessitazione di un teorema senza ipotesi locali. La loro prova
consiste quindi nell'applicare la clausola corrispondente.

**Assiomi con nome.** I risultati `MLK_axiom_addimp`,
`MLK_axiom_distribimp`, `MLK_axiom_doubleneg`, `MLK_axiom_iffimp1`,
`MLK_axiom_iffimp2`, `MLK_axiom_impiff`, `MLK_axiom_true`, `MLK_axiom_not`,
`MLK_axiom_and`, `MLK_axiom_or` e `MLK_axiom_boximp` sono le undici istanze
della base assiomatica elencata nella Sezione 3. Ciascuno segue introducendo
la corrispondente istanza di assioma K.

**Monotonia negli assiomi (`MODPROVES_MONO1`).** Si procede per induzione
sulla derivazione. Un assioma K rimane tale; un elemento di $S$ appartiene a
$S'$ perché $S\subseteq S'$; le ipotesi non cambiano. MP si conserva
applicando l'ipotesi induttiva alle due premesse. Nel caso della
necessitazione, l'ipotesi induttiva trasporta prima il teorema dal sistema
$S$ al sistema $S'$, dopo di che si applica nuovamente la necessitazione.

**Monotonia nelle ipotesi (`MODPROVES_MONO2`).** Anche qui si usa l'induzione
sulla derivazione. Il solo caso non immediato è l'introduzione di un'ipotesi:
se $p\in H$ e $H\subseteq H'$, allora $p\in H'$. Nella necessitazione la
premessa ha contesto vuoto e quindi non dipende né da $H$ né da $H'$.

### 10.2 Calcolo dell'implicazione

**Eliminazione dell'equivalenza (`MLK_iff_imp1`, `MLK_iff_imp2`).** Da
$p\leftrightarrow q$ e dal rispettivo assioma
$(p\leftrightarrow q)\to(p\to q)$, oppure
$(p\leftrightarrow q)\to(q\to p)$, si conclude con MP.

**Antisimmetria (`MLK_imp_antisym`).** Si applica due volte MP all'assioma
$(p\to q)\to((q\to p)\to(p\leftrightarrow q))$.

**Aggiunta di un antecedente (`MLK_add_assum`).** Da $\vdash q$ e
$q\to(p\to q)$, per MP, segue $p\to q$.

**Riflessività (`MLK_imp_refl_th`).** Si considerino

$$
p\to((p\to p)\to p),\qquad p\to(p\to p)
$$

e l'istanza dell'assioma distributivo con $q=p\to p$. Due applicazioni di MP
danno $p\to p$.

**Monotonia sotto un antecedente (`MLK_imp_add_assum`).** Da
$q\to r$ si ottiene $p\to(q\to r)$ per aggiunta di antecedente. MP con
l'assioma distributivo produce $(p\to q)\to(p\to r)$.

**Contrazione (`MLK_imp_unduplicate`).** Applicando l'assioma distributivo a
$p\to(p\to q)$ si ottiene $(p\to p)\to(p\to q)$; MP con la riflessività
conclude.

**Transitività (`MLK_imp_trans`).** Da $q\to r$, il risultato precedente
fornisce $(p\to q)\to(p\to r)$. MP con $p\to q$ conclude.

**Scambio (`MLK_imp_swap`).** Da $p\to(q\to r)$, l'assioma distributivo
produce $(p\to q)\to(p\to r)$. Poiché $q\to(p\to q)$, la transitività
dà $q\to(p\to r)$.

**Catena binaria (`MLK_imp_trans_chain_2`).** Da $p\to q_2$ e
$q_1\to(q_2\to r)$, dopo uno scambio, segue $p\to(q_1\to r)$. Un secondo
scambio e la composizione con $p\to q_1$ danno $p\to(p\to r)$; la
contrazione elimina la duplicazione di $p$.

**Forma interna della transitività (`MLK_imp_trans_th`).** La composizione di
$(q\to r)\to(p\to(q\to r))$ con l'assioma distributivo dà

$$
(q\to r)\to((p\to q)\to(p\to r)).
$$

**Aggiunta della conclusione (`GLimp_add_concl`).** Si scambiano i primi due
antecedenti nella forma interna della transitività e si applica MP a
$p\to q$, ottenendo $(q\to r)\to(p\to r)$.

**Composizione sotto due antecedenti (`MLK_imp_trans2`).** La monotonia sotto
l'antecedente $q$ trasforma $r\to s$ in
$(q\to r)\to(q\to s)$; componendo con $p\to(q\to r)$ si ottiene la tesi.

**Forme interne di scambio e inserimento (`MLK_imp_swap_th`,
`MLK_imp_insert`).** Per la prima si assume $p\to(q\to r)$, si applica la
regola di scambio e si scarica l'assunzione con DT. Per la seconda si compone
$p\to r$ con $r\to(q\to r)$.

### 10.3 Lemma di deduzione

**Direzione di inserimento (`MODPROVES_DEDUCTION_LEMMA_INSERT`).** Da
$H\vdash p\to q$, per monotonia si ha
$H\cup\{p\}\vdash p\to q$. Nello stesso contesto $p$ è un'ipotesi; MP dà
$q$.

**Direzione di cancellazione (`MODPROVES_DEDUCTION_LEMMA_DELETE`).** Si
induce sulla derivazione di $q$ da $H$, supponendo $p\in H$.

- Gli assiomi K e gli elementi di $S$ ricevono l'antecedente $p$ mediante
  aggiunta di assunzione.
- Se la conclusione è un'ipotesi $q$, nel caso $q=p$ si usa $p\to p$;
  altrimenti $q$ resta in $H\setminus\{p\}$ e si aggiunge l'antecedente.
- Nel caso MP, le ipotesi induttive danno $p\to(a\to b)$ e $p\to a$;
  l'assioma distributivo produce $p\to b$.
- Una conclusione ottenuta per necessitazione proviene dal contesto vuoto;
  può quindi essere necessitata anche nel contesto ridotto e poi ricevere
  l'antecedente $p$.

**Lemma di deduzione (`MODPROVES_DEDUCTION_LEMMA`).** La direzione da sinistra
a destra è il lemma di inserimento. Per il converso, se $p\in H$, allora
$H\cup\{p\}=H$ e basta aggiungere l'antecedente. Se $p\notin H$, si
applica il lemma di cancellazione a $H\cup\{p\}$, osservando che
$(H\cup\{p\})\setminus\{p\}=H$.

### 10.4 Falsità, verità e ragionamento classico

**Ex falso (`MLK_ex_falso_th`, `MLK_ex_falso`).** La formula
$\bot\to((p\to\bot)\to\bot)$ è un'istanza di aggiunta di antecedente.
Componendola con l'eliminazione della doppia negazione si ottiene
$\bot\to p$. Se $\bot$ è già derivata, MP dà $p$.

**Contraddizione come antecedente (`MLK_imp_contr_th`).** Si applica la
monotonia sotto l'antecedente $p$ a $\bot\to q$, ottenendo
$(p\to\bot)\to(p\to q)$.

**Ragionamento per assurdo (`MLK_contrad`).** Supponiamo derivata
$(p\to\bot)\to p$. Sotto l'ipotesi $p\to\bot$, MP produce sia $p$ sia
$p\to\bot$, dunque $\bot$. DT dà
$(p\to\bot)\to\bot$, e l'assioma di doppia negazione conclude $p$.

**Casi booleani (`MLK_bool_cases`).** Supponiamo $p\to q$ e
$(p\to\bot)\to q$. Per assurdo assumiamo $q\to\bot$. La prima
implicazione dà $p\to\bot$; la seconda dà allora $q$, in contraddizione
con $q\to\bot$. L'eliminazione della doppia negazione conclude $q$.

**Verità (`MLK_truth_th`).** Dall'assioma
$\top\leftrightarrow(\bot\to\bot)$ si estrae
$(\bot\to\bot)\to\top$; MP con la riflessività di $\bot$ dà $\top$.

**Riflessività, simmetria e transitività dell'equivalenza
(`MLK_iff_refl_th`, `MLK_iff_sym`, `MLK_iff_trans`).** La riflessività segue
dalle due copie di $p\to p$. La simmetria scambia le due implicazioni
estratte da un'equivalenza. La transitività compone separatamente le
implicazioni nelle due direzioni e le ricongiunge per antisimmetria.

### 10.5 Regole modali elementari

**Monotonia della scatola (`MLK_imp_box`).** Da un teorema
$p\to q$ si ottiene $\Box(p\to q)$ per necessitazione; MP con K dà
$\Box p\to\Box q$.

**Modus ponens inscatolato (`MLK_box_modusponens`, `MLK_boximp`,
`MLK_box_moduspones`).** Se è disponibile $\Box(p\to q)$, K e MP danno
$\Box p\to\Box q$, e un'ulteriore applicazione di MP a $\Box p$ dà
$\Box q$. Se si parte dal teorema non inscatolato $p\to q$, si usa prima
la monotonia della scatola.

### 10.6 Congiunzione

**Proiezioni (`MLK_and_left_th`, `MLK_and_right_th`).** Dall'assioma che
caratterizza $p\land q$ si ottiene
$(p\to(q\to\bot))\to\bot$. Per dimostrare $p$, si assume
$p\to\bot$; sotto ulteriori ipotesi $p,q$ si ricava $\bot$, quindi
$p\to(q\to\bot)$, ancora $\bot$, e infine $p$ per doppia negazione.
La prova della proiezione destra è simmetrica.

**Introduzione curried (`MLK_and_pair_th`).** Sotto le ipotesi $p$ e $q$,
per provare la caratterizzazione negativa della congiunzione si assume
$p\to(q\to\bot)$ e si applica due volte MP, ottenendo $\bot$. DT scarica
le tre ipotesi; l'altra direzione dell'assioma della congiunzione dà
$p\to(q\to p\land q)$.

**Regola della congiunzione (`MLK_and`).** Una derivazione di $p\land q$
fornisce entrambe le componenti mediante le proiezioni. Viceversa, da
derivazioni di $p$ e $q$, due MP con il lemma precedente producono
$p\land q$.

**Introduzione ed eliminazione sotto implicazione (`MLK_and_intro`,
`MLK_and_add`, `MLK_and_elim`).** Le prime due combinano
$r\to p$ e $r\to q$ con $p\to(q\to p\land q)$. L'eliminazione compone
$r\to(p\land q)$ con ciascuna proiezione.

**Shunt e antecedente congiunto (`MLK_shunt`, `MLK_ante_conj`,
`MLK_ante_conj2`, `MLK_imp_imp`).** Componendo
$p\to(q\to p\land q)$ con $(p\land q)\to r$ si ottiene
$p\to(q\to r)$. Nel verso opposto si applica la catena binaria alle due
proiezioni. La variante `ante_conj2` premette uno scambio; `imp_imp` raccoglie
le due direzioni.

**Forma interna di MP (`MLK_modusponens_th`).** Da
$(p\to q)\land p$ si proiettano $p\to q$ e $p$, quindi MP dà $q$.

**Definizione dell'equivalenza (`MLK_iff_def_th`, `MLK_iff_def`).** Da
$p\leftrightarrow q$ si estraggono le due implicazioni e le si congiunge.
Viceversa, dalle due proiezioni si applica l'assioma di introduzione
dell'equivalenza. La versione esterna segue applicando MP nelle due direzioni.

### 10.7 Negazione e disgiunzione

**Definizione della negazione e negazione del falso (`MLK_not_def`,
`MLK_not_false`).** Le due direzioni della prima sono ottenute dall'assioma
$\neg p\leftrightarrow(p\to\bot)$. Ponendo $p=\bot$, la riflessività
$\bot\to\bot$ introduce $\neg\bot$.

**Contrapposizione (`MLK_contrapos`).** Da $p\to q$, la composizione verso
$\bot$ dà $(q\to\bot)\to(p\to\bot)$. Le due equivalenze che definiscono
la negazione trasformano questo risultato in $\neg q\to\neg p$.

**Doppia negazione (`MLK_not_not_false_th`, `MLK_not_not_th`,
`MLK_DOUBLENEG_CL`, `MLK_DOUBLENEG`, `MLK_DOUBLENEG_IFF`).** Una direzione di
$((p\to\bot)\to\bot)\leftrightarrow p$ è l'assioma classico; l'altra si
ottiene assumendo $p$ e $p\to\bot$. Sostituendo a ogni negazione la sua
definizione si ricava $\neg\neg p\leftrightarrow p$. Le regole di
introduzione, eliminazione e l'equivalenza esterna seguono con MP.

**Introduzioni della disgiunzione (`MLK_or_right_th`, `MLK_or_left_th`,
`MLK_or_introl`, `MLK_or_intror`).** Supponiamo $p$ e, per assurdo,
$\neg p\land\neg q$. La prima proiezione contraddice $p$, dunque
$\neg(\neg p\land\neg q)$, che per definizione equivale a $p\lor q$.
L'altro lato è simmetrico. Le regole senza implicazione applicano MP.

**Eliminazione della disgiunzione (`MLK_ante_disj`, `MLK_disj_imp`,
`MLK_or_elim`).** Assumiamo $p\lor q$, $p\to r$, $q\to r$. Si ragiona
per casi su $p$, poi su $q$. Se entrambi sono falsi, si ottiene
$\neg p\land\neg q$, in contraddizione con la definizione di $p\lor q$.
Negli altri casi segue $r$. DT produce
$(p\lor q)\to r$. Componendo questa implicazione con le due introduzioni si
ottiene il converso di `MLK_disj_imp`; MP dà `MLK_or_elim`.

**Trasporto dentro una disgiunzione (`MLK_or_transl`, `MLK_or_transr`).** Si
compone l'implicazione data con la corrispondente introduzione della
disgiunzione.

**Regola di Frege (`MLK_frege`).** Due MP con l'assioma distributivo applicati
a $p\to(q\to r)$ e $p\to q$ producono $p\to r$.

**Non contraddizione (`MLK_NC`, `MLK_NC_ALT`, `MLK_nc_th`).** Da
$p\land\neg p$ si proiettano $p$ e $p\to\bot$, quindi MP dà $\bot$.
Da $\bot$, ex falso produce entrambe le componenti. `NC_ALT` compone questo
fatto con ex falso; `nc_th` ne internalizza la prima direzione.

**MP per equivalenza (`MLK_iff_mp`, `MLK_iff`).** Si estrae da
$p\leftrightarrow q$ l'implicazione appropriata e si usa MP. Applicando lo
stesso argomento all'equivalenza simmetrica si ottiene l'equivalenza esterna
fra le due nozioni di derivabilità.

### 10.8 Leggi algebriche e congruenze

**Commutatività e associatività di $\land$ (`MLK_and_comm_th`,
`MLK_and_comm`, `MLK_and_assoc_th`, `MLK_and_assoc`).** Ogni implicazione si
costruisce proiettando le componenti nella disposizione iniziale e
ricongiungendole nella disposizione richiesta. L'antisimmetria produce
l'equivalenza interna; MP produce la versione esterna.

**Commutatività e associatività di $\lor$ (`MLK_or_comm`,
`MLK_or_assoc_left_th`, `MLK_or_assoc_right_th`, `MLK_or_assoc_th`,
`MLK_or_assoc`).** Si elimina la disgiunzione per casi e in ciascun ramo si
usa la sequenza opportuna di introduzioni. Le due implicazioni associative
formano l'equivalenza interna e, mediante MP, quella esterna.

**Monotonia dell'implicazione (`MLK_imp_mono`, `MLK_imp_mono_th`).** Assunti
$p'\to p$, $q\to q'$, $p\to q$ e $p'$, tre MP consecutivi producono
$q'$. Scaricando gli ultimi due antecedenti si ottiene
$(p\to q)\to(p'\to q')$. La forma `*_th` internalizza anche le prime due
premesse, raccolte in una congiunzione.

**Congruenza della congiunzione (`MLK_and_imp`, `MLK_and_subst_th`,
`MLK_and_subst`, `MLK_and_subst_left_th`, `MLK_and_subst_right_th`).** Si
proiettano $p,q$, si applicano rispettivamente $p\to p'$ e $q\to q'$,
quindi si ricongiungono i risultati. Usando in entrambe le direzioni le
implicazioni estratte dalle equivalenze si ottiene la congruenza. Le varianti
sinistra e destra usano la riflessività per l'argomento invariato e DT per
internalizzare l'equivalenza sostituita.

**Congruenza dell'implicazione (`MLK_imp_subst`, `MLK_imp_mp_subst`).** La
monotonia dell'implicazione è contravariante nell'antecedente e covariante nel
conseguente. Si usano quindi $p'\to p$ e $q\to q'$ in una direzione, e le
implicazioni opposte nell'altra. La variante MP trasporta una derivazione
attraverso l'equivalenza ottenuta.

**Congruenza della negazione (`MLK_not_subst`, `MLK_not_subst_th`,
`MLK_iff_not`).** Le due implicazioni dell'equivalenza vengono
contrapposte. Per il converso di `iff_not`, si nega ancora e si eliminano le
doppie negazioni.

**Congruenza della disgiunzione (`MLK_or_subst_th`,
`MLK_or_subst_right`).** Si elimina $p\lor q$. Nel primo ramo si trasporta
$p$ a $p'$ e si introduce la nuova disgiunzione; nel secondo si procede
con $q\to q'$. La direzione inversa usa le implicazioni opposte. La variante
destra pone l'equivalenza riflessiva nel primo argomento.

**Congruenza dell'equivalenza (`MLK_iff_subst`, `MLK_iff_mp_subst`).** Si
riscrivono entrambe le equivalenze come congiunzioni delle due implicazioni,
si applicano le congruenze di implicazione e congiunzione e si torna alla
forma con $\leftrightarrow$. La variante MP applica il risultato a una
derivazione dell'equivalenza originale.

### 10.9 Ulteriori identità classiche

**Idempotenza, unità e contrapposizione interna.** `MLK_iff_and_refl` congiunge
due copie di $p$ in una direzione e proietta nell'altra.
`MLK_and_left_true_th`, `MLK_and_rigth_true_th`, `MLK_or_rid_th` e
`MLK_or_lid_th` combinano proiezioni o eliminazione per casi con i teoremi
$\top$ ed $\bot\to p$. `MLK_contrapos_th` assume $p\to q$, applica la
contrapposizione e usa DT.

**Equivalenza con la contrapposta (`MLK_contrapos_eq_th`,
`MLK_contrapos_eq`).** La direzione diretta è la contrapposizione. Per il
converso si assumono $\neg q\to\neg p$, $p$ e $\neg q$: si ricava
$\neg p$, in contraddizione con $p$; dunque $\neg\neg q$, e quindi
$q$. DT scarica le ipotesi. La variante esterna usa MP nelle due direzioni.

**Terzo escluso e definizione della disgiunzione (`MLK_tnd_th`,
`MLK_and_eq_or`).** La formula $p\lor\neg p$ segue dal ragionamento per casi:
da $p$ si usa l'introduzione sinistra, da $p\to\bot$ si introduce prima
$\neg p$ e poi la disgiunzione. `and_eq_or` è l'applicazione in entrambe le
direzioni dell'assioma che definisce $\lor$.

**De Morgan (`MLK_de_morgan_and_th`, `MLK_de_morgan_or_th`).** Per la prima
legge si sostituiscono $p,q$ con $\neg\neg p,\neg\neg q$ sotto la
congiunzione e la negazione, poi si usa la definizione della disgiunzione. Per
la seconda, $\neg(p\lor q)$ implica separatamente $\neg p$ e $\neg q$
per contrapposizione delle introduzioni. Viceversa, da entrambe le negazioni,
ogni caso della disgiunzione conduce a $\bot$, dunque
$\neg(p\lor q)$.

**Negazione del vero (`MLK_not_true_th`, `MLK_not_true`).** Da $\neg\top$
si ottiene $\top\to\bot$, che applicata al teorema $\top$ dà $\bot$.
Il converso è ex falso. La versione esterna usa l'equivalenza così ottenuta.

**Equivalenze da prove positive o negative (`MLK_proves_iff_pos`,
`MLK_proves_iff_neg`).** Se $p$ e $q$ sono entrambi teoremi, ciascuno può
ricevere l'altro come antecedente, producendo le due implicazioni. Se sono
dimostrate entrambe le negazioni, si applica il caso positivo a
$\neg p,\neg q$ e poi si elimina la negazione da entrambi i lati.

**Introduzione da antecedente falso (`MLK_imp_introl`).** Da $\neg p$ si
ottiene $p\to\bot$, che composto con $\bot\to q$ dà $p\to q$.

**Negazioni di disgiunzione e implicazione (`MLK_proves_not_or`,
`MLK_crysippus_th`, `MLK_proves_not_imp`).** La prima congiunge
$\neg p,\neg q$ e applica De Morgan. Per
$\neg(p\to q)\leftrightarrow p\land\neg q$, la direzione diretta ricava
$p$ per assurdo e $\neg q$ contrapponendo $q\to(p\to q)$; la direzione
inversa assume $p\to q$, usa $p$ per ottenere $q$ e lo contraddice con
$\neg q$. L'ultima regola applica questa equivalenza a prove di $p$ e
$\neg q$.

**Combinazione di conclusioni (`MLK_and_imp_th1`, `MLK_and_imp_th`).** Due
implicazioni con antecedente comune si congiungono mediante l'introduzione
della congiunzione. Se le premesse sono equivalenze, la direzione inversa si
ottiene proiettando una componente e tornando a $p$.

**Simmetria e identità del vero per l'equivalenza (`MLK_iff_sym_th`,
`MLK_iff_true_th`).** La prima assume $p\leftrightarrow q$, scambia le due
implicazioni e scarica l'assunzione. Per
$(p\leftrightarrow\top)\leftrightarrow p$, dalla direzione
$\top\to p$ e dal teorema $\top$ si ricava $p$; viceversa, da $p$ si
ottengono $p\to\top$ e $\top\to p$. Il caso
$(\top\leftrightarrow p)\leftrightarrow p$ è analogo.

**Clausole dell'implicazione (`MLK_imp_clauses`).** Le formule
$p\to\top$ e $\bot\to p$ seguono rispettivamente dall'aggiunta di
antecedente e da ex falso. $p\to\bot$ equivale a $\neg p$ per definizione.
Infine, $\top\to p$ implica $p$ per MP con $\top$, mentre $p$ implica
$\top\to p$ aggiungendo l'antecedente.

**Regole `MLK_imp_truefalse_th`, `MLK_imp_true_rule` e
`MLK_imp_false_rule`.** La prima assume successivamente
$q\to\bot,p,p\to q$: due MP producono $q$, poi $\bot$; DT scarica le
ipotesi. Per `imp_true_rule`, assunto $p\to q$, si ragiona per casi su
$p$: se $p$, si ottiene $q$ e quindi $r$; se $\neg p$, si usa
direttamente $\neg p\to r$. Per `imp_false_rule`, assunto
$(p\to q)\to\bot$, si ragiona prima su $q$. Se $q$, allora
$p\to q$, assurdo. Se $\neg q$, l'ipotesi data produce $p\to r$; un
ulteriore ragionamento per casi su $p$ conclude $r$, perché $\neg p$
renderebbe comunque vera $p\to q$, ancora assurdo.

### 10.10 Distributività

**Distribuzione di $\lor$ con un fattore comune (`MLK_or_and_distr`,
`MLK_or_and_distr_inv`, `MLK_or_and_distr_equiv`).** Da
$(p\lor q)\land r$ si ottengono $p\lor q$ e $r$; eliminando la
disgiunzione si costruisce rispettivamente $p\land r$ oppure $q\land r$,
poi si introduce la disgiunzione finale. Nel verso opposto si elimina
$(p\land r)\lor(q\land r)$; in entrambi i rami si costruiscono
$p\lor q$ e $r$. Le due regole formano l'equivalenza esterna.

**Distribuzione di $\land$ sulla disgiunzione (`MLK_and_or_distr`,
`MLK_and_or_distr_inv_prelim`, `MLK_and_or_distr_inv`,
`MLK_and_or_distr_equiv`).** Da $(p\land q)\lor r$, il primo caso fornisce
sia $p\lor r$ sia $q\lor r$, e il secondo introduce $r$ in entrambe.
Nel converso si elimina prima $p\lor r$: il caso $r$ conclude subito;
nel caso $p$ si elimina $q\lor r$, costruendo $p\land q$ oppure
concludendo ancora con $r$. Il lemma preliminare è la parte di questo
argomento condotta sotto l'ipotesi $q$. Le due direzioni danno
l'equivalenza esterna.

**Forma interna distributiva (`MLK_and_or_ldistrib_th`).** Da
$p\land(q\lor r)$, si applica la prima distribuzione a
$(q\lor r)\land p$ e si commutano le congiunzioni ottenute. Nel verso
opposto si eliminano i due casi $p\land q$ e $p\land r$, mantenendo $p$
e introducendo rispettivamente $q\lor r$. L'antisimmetria conclude
l'equivalenza.

### 10.11 Risultati modali composti

**Congruenza della scatola (`MLK_box_iff_th`, `MLK_box_iff`,
`MLK_box_subst`).** Da $\Box(p\leftrightarrow q)$, si inscatolano le due
implicazioni contenute nell'equivalenza e si usa K per ottenere
$\Box p\to\Box q$ e $\Box q\to\Box p$. La loro antisimmetria dà
$\Box p\leftrightarrow\Box q$. La forma interna si ottiene con DT; se
$p\leftrightarrow q$ è un teorema, la necessitazione fornisce la premessa
inscatolata.

**Scatola e congiunzione (`MLK_box_and`, `MLK_box_and_inv`,
`MLK_box_and_th`, `MLK_box_and_inv_th`).** Dalle due proiezioni
$(p\land q)\to p,q$, monotonia della scatola e MP ricavano
$\Box p,\Box q$ da $\Box(p\land q)$. Viceversa si necessita
$p\to(q\to p\land q)$ e si applica K due volte a $\Box p,\Box q$. Le due
forme con implicazione si ottengono scaricando la premessa con DT.

**Possibilità e congiunzione (`MLK_diam_and_th`).** Contrapponendo le
proiezioni si hanno $\neg p\to\neg(p\land q)$ e
$\neg q\to\neg(p\land q)$. La monotonia della scatola dà
$\Box\neg p\to\Box\neg(p\land q)$ e l'analoga formula per $q$.
Contrapponendo ancora si ottengono
$\Diamond(p\land q)\to\Diamond p$ e
$\Diamond(p\land q)\to\Diamond q$, che vengono congiunte.

### 10.12 Sostituzione uniforme

**Chiusura degli assiomi (`KAXIOM_SUBST`).** Si considerano uno per uno gli
undici schemi primitivi. Sostituire uniformemente le variabili proposizionali
lascia invariata la loro forma esterna e produce quindi un'altra istanza dello
stesso schema.

**Trasporto delle derivazioni (`SUBST_IMP`).** Si induce sulla derivazione.
Gli assiomi K sono trattati dal lemma precedente; un assioma aggiuntivo resta
in $S$ per l'ipotesi di chiusura; un'ipotesi diventa un elemento
dell'immagine sostituita di $H$. MP è preservato perché la sostituzione
commuta con l'implicazione. Nel caso della necessitazione, l'immagine del
contesto vuoto è ancora vuota, quindi si può necessitare la formula
sostituita.

**Sostituzione di equivalenze (`SUBSTITUTION_LEMMA`).** È il caso precedente
applicato alla formula $p\leftrightarrow q$, osservando che la sostituzione
commuta con $\leftrightarrow$.

**Sostituzioni puntualmente equivalenti (`SUBST_IFF`).** Si induce sulla
struttura di $p$. Costanti e atomi seguono rispettivamente dalla
riflessività e dall'ipotesi puntuale. I casi negazione, congiunzione,
disgiunzione, implicazione ed equivalenza usano le rispettive congruenze. Nel
caso $\Box p$, l'ipotesi induttiva nel contesto vuoto e la congruenza della
scatola danno la tesi.

**Falso nel contesto (`MODPROVES_EX_FALSO`).** Se $\bot\in H$, la regola
delle ipotesi dà $S;H\vdash\bot$; MP con $\bot\to p$ conclude
$S;H\vdash p$.
