# Documentazione matematica di HOLMS

Questa cartella contiene l'esposizione in linguaggio naturale delle definizioni,
dei risultati e delle dimostrazioni di HOLMS. La documentazione è essenzialmente
indipendente dalle implementazioni specifiche in HOL Light e Lean: deve poter
essere letta e compresa senza conoscere i linguaggi dei verificatori.

Riferimenti a un'implementazione sono ammessi quando sono particolarmente
importanti per comprendere il significato o la portata di un risultato. I nomi
dei risultati possono aiutare a ritrovarli nel codice, ma non sostituiscono gli
enunciati e le spiegazioni matematiche.

## Capitoli disponibili

| Argomento | Esposizione matematica | Note sulla traduzione |
|---|---|---|
| Sintassi, sottoformule, semantica di Kripke e bisimulazione | [Modal](Modal.md) | [HOLMS.Modal](../lean/translation/Modal.md) |
| Calcolo assiomatico, derivabilità e regole derivate | [Calculus](Calculus.md) | [HOLMS.Calculus](../lean/translation/Calculus.md) |

## Rapporto con la documentazione della traduzione

La cartella [`lean/translation`](../lean/translation/README.md) documenta la
traduzione da HOL Light a Lean: corrispondenze con i sorgenti, scelte di
rappresentazione, adattamenti delle dimostrazioni, compatibilità dei nomi e
materiale non riprodotto. Questi dettagli appartengono alle note di traduzione,
mentre qui si espone la matematica che le implementazioni formalizzano.

Le convenzioni di traduzione comuni a più moduli sono raccolte in
[`lean/CONVENTIONS.md`](../lean/CONVENTIONS.md).

Quando si aggiunge un capitolo, aggiornare questo indice e collegarlo alla nota
di traduzione pertinente, se disponibile. Le note di traduzione devono a loro
volta rimandare al capitolo matematico corrispondente, senza duplicarne
l'esposizione.
