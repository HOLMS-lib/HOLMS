# Sintassi e semantica della logica modale in HOLMS

Questo capitolo descrive la teoria matematica formalizzata in `modal.ml` e in
`Modal.lean`. L'esposizione non dipende dal linguaggio del verificatore e
include le dimostrazioni in linguaggio naturale dei risultati presenti nel
modulo.

## 1. Formule modali

Il linguaggio contiene le formule

$$
p ::= \bot \mid \top \mid a \mid \neg p \mid p\land p
      \mid p\lor p \mid p\to p \mid p\leftrightarrow p \mid \Box p,
$$

dove $a$ varia in un insieme numerabile di nomi di variabili
proposizionali. I diversi costruttori sono disgiunti e iniettivi: per esempio,
$\Box p=\Box q$ implica $p=q$, mentre una formula inscatolata non può
essere uguale a una congiunzione.

Due operatori sono definiti a partire da quelli primitivi:

$$
\Diamond p := \neg\Box\neg p,
\qquad
\boxdot p := \Box p\land p.
$$

Il primo è la possibilità, duale della necessità. Il secondo, chiamato
`Dotbox` nell'originale, raccoglie la necessità di $p$ e $p$ stesso.

### 1.1 Costituenti terminali e profondità

I **costituenti terminali** di una formula sono le occorrenze, considerate
come insieme, di $\bot$, $\top$ e delle formule atomiche. Negazione e
scatola non aggiungono costituenti; un connettivo binario unisce quelli dei
due argomenti.

La profondità sintattica è zero per costanti e atomi, aumenta di uno sotto
negazione e scatola, ed è uno più del massimo delle profondità dei due
argomenti per i connettivi binari.

Il tipo di tutte le formule è numerabile. Intuitivamente, ogni formula è un
albero finito i cui nodi appartengono a un insieme finito di costruttori e le
cui foglie atomiche hanno nomi presi da un insieme numerabile.

## 2. Costituenti immediati e sottoformule

Una formula $p$ è un **costituente immediato** di $q$, scritto qui
$p\prec q$, nei casi seguenti:

- $p\prec\neg p$ e $p\prec\Box p$;
- ciascuno dei due argomenti è costituente immediato di una congiunzione,
  disgiunzione, implicazione o equivalenza.

Le costanti e gli atomi non hanno costituenti immediati.

La relazione di sottoformula, indicata con $p\preceq q$, è la chiusura
riflessiva e transitiva di $\prec$. Pertanto ogni formula è sottoformula di
se stessa e ogni costituente, anche a profondità arbitraria, è una
sottoformula.

### 2.1 Equazioni di inversione

La relazione è caratterizzata ricorsivamente da:

$$
p\preceq\bot \iff p=\bot,
\qquad
p\preceq\top \iff p=\top,
$$

$$
p\preceq a \iff p=a,
$$

$$
p\preceq\neg q \iff p=\neg q\ \lor\ p\preceq q,
$$

$$
p\preceq(q\circ r)
\iff p=q\circ r\ \lor\ p\preceq q\ \lor\ p\preceq r,
$$

per $\circ\in\{\land,\lor,\to,\leftrightarrow\}$, e

$$
p\preceq\Box q \iff p=\Box q\ \lor\ p\preceq q.
$$

Queste equivalenze consentono sia di enumerare le sottoformule sia di
ragionare per inversione sull'ultimo costruttore.

### 2.2 Finitezza

Ogni formula ha un numero finito di sottoformule. Più precisamente, si può
costruire ricorsivamente un insieme finito:

- una foglia contribuisce soltanto se stessa;
- un operatore unario aggiunge la formula composta alle sottoformule del suo
  argomento;
- un operatore binario aggiunge la formula composta all'unione delle
  sottoformule dei due argomenti.

Ne segue anche la finitezza della famiglia di tutti gli insiemi contenuti
nell'unione fra le sottoformule di $p$ e le loro negazioni. Questa
osservazione sarà utile nelle costruzioni canoniche e nelle procedure di
decisione.

Infine, le sottoformule possono essere enumerate da una lista senza
ripetizioni.

## 3. Semantica di Kripke

Un **frame di Kripke** è una coppia

$$
F=(W,R),
$$

dove $W$ è l'insieme dei mondi e $R$ è la relazione di accessibilità. Il
tipo ambiente può contenere oggetti che non appartengono a $W$; la validità
viene sempre valutata nei mondi appartenenti al frame.

Una **valutazione** $V$ assegna a ogni variabile proposizionale l'insieme
dei mondi in cui essa è vera. Un **modello** è un frame corredato da una
valutazione.

La relazione di soddisfacimento $F,V,w\models p$ è definita
ricorsivamente:

$$
F,V,w\not\models\bot,
\qquad
F,V,w\models\top,
$$

$$
F,V,w\models a \iff V(a,w),
$$

e i connettivi proposizionali ricevono la consueta interpretazione classica.
Per la necessità:

$$
F,V,w\models\Box p
\iff
\forall w'\in W,\; R(w,w')\Rightarrow F,V,w'\models p.
$$

Quindi sono rilevanti soltanto i successori accessibili che appartengono
all'insieme dei mondi del frame.

Una formula è **valida nel frame** $F$, scritto $F\models p$, se è vera
in ogni mondo di $F$ per ogni valutazione. È **valida in una classe di
frame** $L$, scritto $L\models p$, se è valida in ogni frame di $L$.

## 4. Interpretazioni arbitrarie delle formule

Un semplice ma utile lemma osserva che, fissato un frame, le interpretazioni
delle formule al variare della formula e della valutazione comprendono tutti
i predicati sui mondi. Infatti, dato un predicato arbitrario $U$, basta
scegliere una variabile atomica e valutarla esattamente come $U$.

Di conseguenza, per ogni proprietà $P$ dei predicati sui mondi,

$$
\bigl(\forall p,V,\;P(\llbracket p\rrbracket_V)\bigr)
\iff
\bigl(\forall U,\;P(U)\bigr).
$$

Questo principio permette di trasformare alcuni schemi modali in proprietà
del primo ordine della relazione di accessibilità.

## 5. Bisimulazione

Consideriamo due modelli

$$
M_1=(W_1,R_1,V_1),
\qquad
M_2=(W_2,R_2,V_2).
$$

Una relazione $Z$ fra i loro mondi è una **bisimulazione** se, ogni volta
che $Z(w_1,w_2)$, valgono le condizioni seguenti.

1. $w_1\in W_1$ e $w_2\in W_2$.
2. Gli stessi atomi sono veri nei due mondi:
   $V_1(a,w_1)\iff V_2(a,w_2)$ per ogni $a$.
3. **Forth:** per ogni $w'_1$ con $R_1(w_1,w'_1)$, esiste
   $w'_2\in W_2$ tale che $R_2(w_2,w'_2)$ e $Z(w'_1,w'_2)$.
4. **Back:** simmetricamente, ogni successore di $w_2$ può essere
   accoppiato con un successore di $w_1$ tramite $Z$.

Due modelli puntati $(M_1,w_1)$ e $(M_2,w_2)$ sono **bisimili** se esiste
una bisimulazione che mette in relazione $w_1$ e $w_2$.

Il risultato fondamentale è l'**invarianza per bisimulazione**:

$$
Z(w_1,w_2)
\quad\Longrightarrow\quad
\bigl(M_1,w_1\models p\iff M_2,w_2\models p\bigr)
$$

per ogni formula modale $p$.

## 6. Trasferimento della validità

L'invarianza consente di trasferire la validità fra frame o classi di frame.
Se ogni modello puntato basato su $F_1$ è bisimile a un modello puntato
basato su $F_2$, allora ogni formula valida in $F_2$ è valida in $F_1$.

Più in generale, siano $L_1,L_2$ due classi di frame. Se per ogni frame di
$L_1$, ogni valutazione e ogni suo mondo esiste un modello puntato bisimile
costruito su un frame di $L_2$, allora

$$
L_2\models p \quad\Longrightarrow\quad L_1\models p.
$$

La direzione del trasferimento è importante: la verità viene prelevata dal
modello o dalla classe di destra e riportata, tramite l'equivalenza
bisimulativa, al modello o alla classe di partenza.

## 7. Dimostrazioni dei risultati

### 7.1 Numerabilità delle formule

**Teorema `countable` (`Form.countable`).** I nomi atomici formano un insieme
numerabile.
Per ogni altezza $n$, le formule di profondità minore di $n$ sono
numerabili: il caso base contiene soltanto le costanti e gli atomi; al passo
induttivo si aggiungono immagini e prodotti finiti di insiemi numerabili,
corrispondenti agli operatori unari e binari. Ogni formula ha profondità
finita, quindi l'insieme di tutte le formule è un'unione numerabile di insiemi
numerabili, ed è pertanto numerabile.

### 7.2 Costituenti immediati

**Teoremi `not_minor_falsum`, `not_minor_verum`, `not_minor_atom`.** Nessuna
regola che genera $p\prec q$ ha come secondo membro $\bot$, $\top$ o un
atomo. L'esistenza di un tale costituente è quindi impossibile.

**Teorema `minor_neg_iff`.** L'unica regola che termina in $\neg q$ dichiara
$q\prec\neg q$. Dunque $p\prec\neg q$ implica $p=q$, e l'uguaglianza
permette di applicare la stessa regola nel verso opposto.

**Teoremi `minor_conj_iff`, `minor_disj_iff`, `minor_imp_iff`,
`minor_iff_iff`.** Per ciascun connettivo binario esistono esattamente due
regole: il primo e il secondo argomento sono costituenti immediati. Perciò
$p\prec(q\circ r)$ equivale a $p=q\lor p=r$.

**Teorema `minor_box_iff`.** Come per la negazione, l'unico costituente
immediato di $\Box q$ è $q$.

### 7.3 Proprietà generali delle sottoformule

**Teorema `Minor.subformula`.** Se $p\prec q$, si parte dalla riflessività
$p\preceq p$ e si aggiunge il singolo passo immediato da $p$ a $q$.

**Teorema `Subformula.trans`.** Si induce sul cammino che testimonia
$q\preceq r$. Se il cammino è riflessivo non c'è nulla da aggiungere. Se
termina con un passo immediato, si applica l'ipotesi induttiva alla parte
iniziale e si riaggiunge l'ultimo passo.

**Teoremi `Subformula.trans_minor` e `Minor.trans_subformula`.** Il primo
aggiunge un passo immediato in coda a un cammino di sottoformula. Per il
secondo si trasforma prima il passo immediato iniziale in una relazione di
sottoformula e poi si usa la transitività.

**Teorema `subformula_cases_tail_iff`.** Una derivazione di
$p\preceq q$ è riflessiva, e allora $p=q$, oppure termina con un passo
$r\prec q$ preceduto da $p\preceq r$. Viceversa, ciascuna delle due
alternative costruisce una derivazione.

**Teorema `subformula_cases_head_iff`.** Si induce sulla derivazione. Nel caso
riflessivo vale $p=q$. Nel caso esteso, se la parte precedente era
riflessiva, l'ultimo passo è anche il primo; altrimenti si conserva il primo
passo già individuato e si prolunga il cammino restante. Il converso usa la
riflessività oppure antepone il passo immediato dato.

### 7.4 Inversione delle sottoformule

**Teoremi `subformula_falsum_iff`, `subformula_verum_iff`,
`subformula_atom_iff`.** Si applica la caratterizzazione per l'ultimo passo.
Poiché costanti e atomi non hanno costituenti immediati, resta soltanto il caso
riflessivo.

**Teoremi `subformula_neg_iff` e `subformula_box_iff`.** Una sottoformula è la
formula composta stessa oppure raggiunge il suo unico costituente immediato;
in quest'ultimo caso è precisamente una sottoformula dell'argomento.

**Teoremi `subformula_conj_iff`, `subformula_disj_iff`,
`subformula_imp_iff`, `subformula_iff_iff`.** Ancora per la caratterizzazione
dell'ultimo passo, una sottoformula è la formula composta stessa oppure arriva
a uno dei due costituenti immediati. Per transitività, questi due casi sono
esattamente le sottoformule del primo e del secondo argomento.

### 7.5 Discesa attraverso una formula composta

**Teoremi `of_subformula_neg`, `of_subformula_box`.** L'argomento è un
costituente immediato della formula negata o inscatolata. Se quest'ultima è
sottoformula di $q$, si antepone quel passo al cammino esistente.

**Teoremi `of_subformula_conj_left`, `of_subformula_conj_right`,
`of_subformula_disj_left`, `of_subformula_disj_right`,
`of_subformula_imp_left`, `of_subformula_imp_right`,
`of_subformula_iff_left`, `of_subformula_iff_right`.** In ciascun caso si usa
il fatto che l'argomento scelto è un costituente immediato della formula
binaria, quindi lo si antepone al cammino che dalla formula composta conduce a
$q$.

### 7.6 Enumerazione e finitezza delle sottoformule

**Teorema `mem_subformulas_iff`.** Si induce sulla struttura della formula.
Per una foglia, l'insieme costruito contiene soltanto la foglia stessa, come
richiesto dall'inversione. Per un operatore unario, l'insieme contiene la
formula composta e l'insieme ricorsivo dell'argomento. Per un operatore
binario contiene la formula composta e l'unione dei due insiemi ricorsivi.
Le ipotesi induttive e le equazioni di inversione mostrano in ogni caso che
l'appartenenza coincide con la relazione di sottoformula.

**Teorema `finite_subformulas`.** L'insieme astratto
$\{q:q\preceq p\}$ coincide, per il teorema precedente, con l'insieme
finito costruito ricorsivamente. È dunque finito.

**Teorema `finite_subsets_subformulas`.** Le sottoformule sono finite e anche
la loro immagine mediante la negazione è finita. La loro unione è finita; la
famiglia di tutti i suoi sottoinsiemi, cioè il suo insieme delle parti, è
quindi finita.

**Teorema `subformula_list`.** Si prende una qualunque enumerazione senza
ripetizioni dell'insieme finito delle sottoformule. L'assenza di duplicati è
garantita dalla costruzione dell'enumerazione e la caratterizzazione dei suoi
elementi segue da `mem_subformulas_iff`.

### 7.7 Semantica

**Teorema `holdsIn_iff`.** Essere valida in un frame significa, per
definizione, essere vera per ogni valutazione e ogni mondo appartenente al
frame. Le due parti dell'equivalenza sono dunque la stessa proprietà.

**Teorema `holds_forall_iff`.** Se $P$ vale per l'interpretazione di ogni
formula sotto ogni valutazione, sia $U$ un predicato arbitrario sui mondi.
Si sceglie un atomo $a$ e una valutazione che assegna ad $a$ esattamente
$U$; l'interpretazione di $a$ è allora $U$, quindi $P(U)$. Nel verso
opposto, se $P$ vale per ogni predicato, vale in particolare per il
predicato dei mondi che soddisfano una data formula sotto una data
valutazione.

### 7.8 Invarianza per bisimulazione

**Teorema locale `holds_iff` (`Bisimulation.holds_iff`).** Si induce sulla
formula $p$.

- Per $\bot$ e $\top$ l'equivalenza è immediata.
- Per un atomo è esattamente la clausola atomica della bisimulazione.
- Negazione, congiunzione, disgiunzione, implicazione ed equivalenza seguono
  direttamente dalle ipotesi induttive sui costituenti.
- Sia infine $p=\Box q$. Supponiamo $M_1,w_1\models\Box q$ e prendiamo un
  successore $w'_2$ di $w_2$. La clausola back fornisce un successore
  $w'_1$ di $w_1$ con $Z(w'_1,w'_2)$. La premessa inscatolata rende
  vero $q$ in $w'_1$, e l'ipotesi induttiva lo trasferisce a $w'_2$.
  Questo prova $M_2,w_2\models\Box q$. La direzione opposta usa allo stesso
  modo la clausola forth.

### 7.9 Bisimilarità e validità

**Teorema locale `mem_worlds` (`Bisimilar.mem_worlds`).** Dalla bisimilarità
si estrae una bisimulazione $Z$ con $Z(w_1,w_2)$. La prima clausola della bisimulazione
afferma precisamente che i due punti appartengono ai rispettivi insiemi di
mondi.

**Teorema locale `holds_iff` (`Bisimilar.holds_iff`).** Si sceglie la
bisimulazione testimone della bisimilarità e si applica il teorema di invarianza precedente alla coppia di
mondi collegata.

**Teorema `Form.holdsIn_of_bisimilar`.** Supponiamo $p$ valida in $F_2$.
Fissiamo una valutazione $V_1$ e un mondo $w_1$ di $F_1$. Per ipotesi
esistono $V_2,w_2$ tali che i modelli puntati siano bisimili. Il punto
$w_2$ appartiene a $F_2$, quindi la validità rende vero $p$ in
$(F_2,V_2,w_2)$. L'invarianza per bisimilarità trasferisce la verità a
$(F_1,V_1,w_1)$. Poiché valutazione e mondo erano arbitrari, $p$ è valida
in $F_1$.

**Teorema `Form.valid_of_bisimilar`.** Supponiamo $p$ valida in ogni frame
di $L_2$. Presi un frame $F_1\in L_1$, una valutazione e un mondo di
$F_1$, l'ipotesi fornisce un frame $F_2\in L_2$ e un modello puntato
bisimile. La validità in $L_2$ rende vero $p$ nel secondo punto;
l'invarianza lo trasferisce al primo. L'arbitrarietà di frame, valutazione e
mondo conclude $L_1\models p$.

## 8. Quadro complessivo

Il modulo stabilisce quattro fatti strutturali fondamentali:

1. le formule modali costituiscono un insieme numerabile di alberi sintattici
   finiti;
2. ogni formula possiede un insieme finito ed enumerabile di sottoformule;
3. la semantica di Kripke interpreta composizionalmente tutti i connettivi;
4. la verità modale, la validità nei frame e la validità nelle classi di frame
   sono invarianti sotto opportune corrispondenze bisimulative.

Questi risultati forniscono la base sintattica e semantica usata dai moduli
successivi per corrispondenza, correttezza, completezza, decidibilità e
costruzione di contromodelli.
