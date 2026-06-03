# HarperMatcherCL
Experimentálna verifikácia Harperovho algoritmu pre rozpoznávanie regulárnych výrazov v CL

# Kompilácia a Štruktúra projektu

Projekt sa nachádza v priečinku src.

Projekt je možné skompilovať príkazom:

```bat
make.bat
```

## Štruktúra projektu

Verifikácia pozostáva zo štyroch hlavných modulov:

### `msyntax.cl`

Implementuje aritmetizáciu syntaxe regulárnych výrazov spolu s pomocnými funkciami a predikátmi.

### `msemantics.cl`

Obsahuje aritmetizáciu sémantiky regulárnych výrazov a odvodenie ich základných vlastností.

### `mnorm.cl`

Implementuje Harperov postup normalizácie regulárnych výrazov.

### `mmatcher.cl`

Obsahuje:

* implementáciu naivného algoritmu,
* dokazovanie vlastností pomocou simulácie paradigmy totálneho deklaratívneho programovania,
* verifikáciu Harperovho algoritmu.

## Podporné moduly

Nasledujúce moduly poskytujú pomocnú infraštruktúru:

### `mtex.cl`

Definície TeX šablón pre zobrazovanie matematických symbolov.

### `mdebug.cl`

Funkcie a predikáty určené na ladenie a diagnostiku.

### `maux.cl`

Implementácie vybraných pomocných a všeobecne známych funkcií.

