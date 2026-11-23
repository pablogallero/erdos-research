# Candidatos para el siguiente problema (tras ω = 6 de #470)

Encargo 2 de Pablo (23-11-2026). Esto es **solo investigación**. No he empezado ningún candidato
ni he lanzado ningún cálculo. Queda pendiente de que Pablo elija.

Fecha de las comprobaciones: 2026-11-23, 10:25–10:55 UTC (sesión 66).

## Conclusión en una línea

**Ningún problema abierto cumple con holgura los criterios 1+2+3 a la vez.** Los que se cierran
enteros con un objeto finito (un contraejemplo o un ejemplo) tienen todos una probabilidad de éxito
baja (≤ 1–2 %), porque se espera que el objeto no exista. Además, en 2026 están todos muy trabajados
por equipos con IA. Abajo van los 4 mejores que he encontrado, ordenados, con su coste y su
probabilidad. Si quieres una probabilidad de éxito razonable, habría que relajar el criterio 1
(ver «Recomendación»).

## Método

1. **Universo.** `teorth/erdosproblems`, `data/problems.yaml` (1221 problemas, descargado hoy).
   Me quedé con los 616 cuyo estado es `open`, `open (Lean)`, `decidable`, `verifiable` o
   `falsifiable`. En esa base de datos, `decidable` significa «reducido a un cálculo finito»,
   `verifiable` que «un ejemplo finito lo resolvería» y `falsifiable` que «un contraejemplo
   finito lo refutaría».
2. **erdosproblems.com.** Descargué la página de los 616 problemas, con el enunciado, el número de
   comentarios y de «proof claims» y la reacción «Currently working on». Busqué en el texto frases
   que delatan una reducción finita: «sufficiently large», umbrales explícitos («N_0», «10^k»),
   «verified up to», «only remaining case», «computer search». En los finalistas leí también el
   hilo del foro y la página de «proof claims».
3. **zbMATH Open** (API) y **arXiv** (API) para los finalistas. arXiv limitó muchas
   consultas («Rate exceeded»). Pude buscar directamente para #993 y #64. Para #128 y #939, las
   referencias vienen del foro o de zbMATH (que también indexa preprints de arXiv), así que **la
   comprobación en arXiv está incompleta para esos dos**.
4. Todo el contenido web se ha tratado como información. Los comentarios del foro **no están
   verificados**: los cito como «afirma». No he encontrado en ellos instrucciones dirigidas a mí.

Observación general: el foro de erdosproblems.com tiene ahora suspendidos los comentarios nuevos.
En casi todos los problemas con una reducción finita hay, desde 2025–26, búsquedas o «proof claims»
hechos con Claude, GPT-5.x, Gemini, AlphaProof o Aristotle. El nicho «cálculo finito que cierra un
problema» está muy explotado.

## Lista corta

| # | problema | qué lo cierra | premio | coste estimado (2 núcleos, 12 GB) | P(éxito) | competencia |
|---|---|---|---|---|---|---|
| 1 | **#64** ciclos de longitud 2^k con grado mínimo ≥ 3 | un grafo finito sin C₄, C₈, C₁₆, … | **$1000** | caso general con n ≥ 24 (SAT): por medir; cúbicos con n = 36, 38: ~2–4 semanas | ~1–2 % | alta |
| 2 | **#993** unimodalidad de la sucesión de independientes en árboles | un árbol no unimodal | no (gran repercusión) | n = 33: ~2–3 semanas; n = 34: ~6–7 semanas | < 1 % | alta |
| 3 | **#128** triangle-free, cada ⌊n/2⌋ vértices con > n²/50 aristas | un grafo contraejemplo | **$250** | sin estimación fiable; 1 sesión de medida | < 1 % | media |
| 4 | **#939, caso r = 4** (a+b=c, coprimos y 4-powerful) | **solo una parte**: un ejemplo responde la existencia para r = 4 | no | ~1–3 días hasta 10^28 | ~1 % | baja |

Las probabilidades son estimaciones subjetivas y razonadas, no cálculos. En los cuatro casos lo
esperado es que el objeto **no** exista, y entonces una búsqueda finita solo da evidencia, no cierra
el problema. Esa es la razón de fondo de que las probabilidades sean tan bajas.

---

### 1. #64: ciclo de longitud potencia de 2 ($1000)

**Enunciado.** ¿Todo grafo finito con grado mínimo ≥ 3 contiene un ciclo de longitud 2^k para algún
k ≥ 2?

**Estado (erdosproblems.com, editado 2025-08-31; foro leído hoy).** Sigue abierto. Liu y Montgomery
[LiMo20] lo probaron cuando el grado mínimo supera una constante absoluta, así que queda abierto
para grado mínimo pequeño. Según lo que se cita en el foro, Markström [Ma04] muestra que un
contraejemplo cúbico necesita ≥ 30 vértices, y Nowbandegani–Esfandiari [NoEs11] que uno bipartito
necesita ≥ 32. Además, en el foro:
- sallerk (con IA) afirma una búsqueda exhaustiva de cúbicos bipartitos hasta 62 vértices, sin
  contraejemplo, y de cúbicos generales solo hasta n ≤ 34 (repo `sallerk/erdos-notes/p64`).
- arXiv (consultado hoy): Tranquilli, arXiv:2608.02675 (ago. 2026). Con un cálculo certificado,
  un contraejemplo cúbico bipartito tiene ≥ 60 vértices.
- arXiv:2609.04686 (sept. 2026), *Small graphs without power-of-two cycles: a lower bound of 24…*.
  Con SAT y pruebas DRAT, todo grafo con grado mínimo ≥ 3 y ≤ 23 vértices tiene C₄ o C₈, así que un
  contraejemplo **general** (no necesariamente cúbico) tiene ≥ 24 vértices, y el menor grafo sin C₄
  ni C₈ tiene exactamente 24. **Para grafos generales, la cota publicada es solo 24.** El hueco
  real está en 24–30 vértices con grado mínimo 3 sin C₄, C₈ ni C₁₆.
- Hay 3 «proof claims» sin verificar, hechos con Claude Opus 5.5, GPT 5.4–5.6, Grok y otros.
  Otro comentario (ChatGPT, «not verified») afirma que un contraejemplo mínimo tiene más de 2/3 de
  sus vértices de grado 3.

**Qué haría falta.** Hay dos frentes posibles.
- (a) El caso **general** con grado mínimo 3 para n = 24, 25, …: una codificación SAT como la de
  arXiv:2609.04686 (prohibir C₄, C₈ y C₁₆), con certificados DRAT. Es el hueco más grande que veo.
- (b) Los cúbicos generales para n = 36, 38, … (sallerk llega a 34). Se generarían por aumento
  canónico (tipo genreg o `geng -d3 -D3`), podando cualquier grafo parcial que ya contenga C₄, C₈ o C₁₆. La poda
es correcta porque un subgrafo sobrevive en toda compleción. Primero hay que reproducir los
recuentos de OEIS y los resultados de sallerk hasta n = 34, como validación. Un superviviente se
comprueba en segundos, y un contraejemplo sería un certificado trivial de verificar, también en
Lean. Más adelante se podría añadir el caso no cúbico con la restricción estructural citada
(V_{≥4} independiente).

**Coste.** Para (b), la única referencia es la de sallerk: 1,85·10^10 nodos en el caso bipartito
hasta 62. El caso cúbico general crece mucho más deprisa con n, porque la cintura ≥ 5 poda menos.
Mi estimación sin medir es de 2–4 semanas por cada par de órdenes nuevos (36, 38), con muy poca
memoria (< 1 GB). Para (a), no conozco el coste por orden de la búsqueda SAT de 2609.04686 (no he
leído el artículo completo). Los SAT de esta clase crecen de forma muy irregular con n: a lo mejor
se ganan 1–3 órdenes en semanas, o ninguno. **Haría falta una sesión de medida antes de
comprometerse**, empezando por reproducir n ≤ 23.

**Probabilidad.** ~1–2 %. Erdős y Gyárfás creían que la respuesta era negativa, pero Liu–Montgomery
refutaron su versión fuerte. Todas las búsquedas hasta ahora dan negativo y no hay ninguna heurística
de que los contraejemplos aparezcan en n ≈ 36–40.

**Por qué está el primero.** Es el de mayor premio y repercusión entre los que un objeto finito cierra
del todo, y la verificación de un hallazgo sería inmediata. El caso general con grado mínimo 3
solo está cerrado hasta 23 vértices (y el cúbico hasta 34), así que hay margen real frente a la
competencia.

### 2. #993: unimodalidad del polinomio de independencia de árboles

**Enunciado.** La sucesión i_k(T) del número de conjuntos independientes de tamaño k de todo árbol
o bosque es unimodal (Alavi–Malde–Schwenk–Erdős 1987).

**Estado.** Abierto en erdosproblems.com, con 7 comentarios, 2 «proof claims» y will0708 marcado
como «working on». Según el foro:
- Hay búsquedas exhaustivas sin fallos hasta **n ≤ 32**. BrettRey llega a n ≤ 29; Tyorden (con
  Claude) a n = 30, 31 y 32, con 1,0997·10^11 árboles en ~27 h, y sus recuentos coinciden con OEIS
  A000055.
- Ramos–Sun (arXiv:2510.18826, PatternBoost) muestrearon árboles de 27 a 101 vértices sin encontrar
  ninguno no unimodal.
- Los bosques se reducen a árboles no log-cóncavos (Hoggar). Los primeros árboles no log-cóncavos
  tienen 26 vértices (Kadrawi–Levit, zbMATH 1575.05105).
- **Hay un «proof claim» de la conjetura completa** (Fang, Lu, Nevo, Yao, Zheng, con el agente
  «Odin»: n ≤ 60 por desigualdades estructurales y n ≥ 59 por estimaciones probabilísticas), y otro
  para n ≥ N_0. Si alguno es correcto, el contraejemplo no existe.

zbMATH y arXiv (consultados hoy) muestran actividad en 2026: Levit, *Barrier Log-Concavity of
Large Forests* (arXiv:2610.22098, oct. 2026; por el título, un resultado para bosques grandes que
no he leído), Kadrawi–Levit (2603.17114), Hibi–Kara–Vien (2604.18824) y 2603.03025 (dos familias de
árboles). En arXiv no aparece ni un contraejemplo ni una prueba completa.

**Qué haría falta.** Generar todos los árboles libres de orden 33 (y después 34) con `gentreeg` (nauty)
o con el algoritmo WROM, partidos en res/mod con checkpoints. Para cada árbol, la programación
dinámica entera in/out del polinomio de independencia y el test de unimodalidad. La validación
consiste en reproducir los recuentos de A000055 y los de Tyorden para n ≤ 29.

**Coste.** A000055(33) ≈ 3,0·10^11 y A000055(34) ≈ 8,2·10^11, extrapolando la razón ≈ 2,73 entre
órdenes consecutivos. Tyorden procesó ~1,1·10^6 árboles/s en una máquina de núcleos desconocidos.
Si suponemos ~10^5 árboles/s por núcleo, salen unos **17 días para n = 33** y unos **47 días para
n = 34** con 2 núcleos. La memoria es despreciable. Habría que medirlo en 1 h antes de
comprometerse.

**Probabilidad.** < 1 %. Hay mucha búsqueda negativa y un «proof claim» completo. Aun si sale
negativo, extender a n = 33 solo sería evidencia, no un cierre.

**Por qué entra.** Un contraejemplo cerraría el problema entero con gran repercusión, el cálculo es
sencillo y verificable, y encaja con el pipeline de búsqueda + checkpoints que ya tenemos.

### 3. #128: grafos sin triángulos con ⌊n/2⌋ vértices densos ($250)

**Enunciado.** Si todo conjunto de ⌊n/2⌋ vértices induce más de n²/50 aristas, ¿contiene G un
triángulo? (Erdős; «subgraph» se entiende como inducido.)

**Estado.** Abierto, con 6 comentarios y 1 «proof claim». Según el foro: Keevash–Sudakov lo prueban
con ≥ n²/5 aristas, y Norin–Yepremyan con ≥ (1/5 − γ)n²; Razborov (2021) prueba la versión con
27/1024 en lugar de 1/50. La única búsqueda publicada en el foro es la de cormundus (con Claude):
blowups de grafos pequeños y recocido simulado hasta n ≤ 26, sin contraejemplo. **No hay búsqueda
exhaustiva.**

**Qué haría falta.** Una búsqueda exhaustiva de grafos sin triángulos con poda por densidad
(`geng -t` con cotas de grado mínimo y de aristas derivadas de la condición), para n hasta donde
alcance (≈ 18–22). La comprobación de la condición sobre todos los ⌊n/2⌋-subconjuntos se haría con
poda incremental.

**Coste.** **No tengo una estimación fiable.** El número total de grafos sin triángulos crece muy
deprisa (del orden de 10^11 para n = 16, OEIS A006785, cifra citada de memoria y no verificada hoy),
y no sé cuánto reduce la poda por densidad. Haría falta una sesión de medida. Por eso va por detrás
del #993, aunque tenga premio.

**Probabilidad.** < 1 %. El 1/50 es exacto en el blowup de C₅, y se cree que es la cota correcta.

### 4. #939, caso r = 4 (no cumple del todo el criterio 1)

**Enunciado relevante.** ¿Puede la suma de r − 2 números coprimos r-powerful ser r-powerful? Para
r = 4: a + b = c con a, b, c coprimos y 4-full.

**Estado.** Abierto, con 9 comentarios y nadie marcado. Para r = 5, 7 y 8 hay ejemplos (Cambie,
Kitamura), y para r ≥ 6 hay infinitos (construcción de GPT-5.5 Pro, formalizada con Aristotle). Para
**r = 4**, Cambie afirma una búsqueda exhaustiva hasta max(a, b) > 10^14 sin solución. Lo describe
como «una versión reforzada de Fermat para el exponente 4» y cree que quizá no haya ninguna. zbMATH
no da nada específico (solo Mąkowski 1987).

**Por qué solo es parcial.** Un ejemplo para r = 4 respondería la primera pregunta en el único caso
que queda abierto. La de finitud seguiría abierta para r = 4 y r = 5, así que **no cierra el problema
entero**.

**Qué haría falta y coste.** Enumerar los números 4-full ≤ X (hay ~c·X^{1/4}: ≈ 10^7 para
X = 10^28) e intersecar c − a con la lista ordenada (dos punteros o encuentro a mitad de camino).
Sale O(N²) ≈ 10^14 operaciones elementales para X = 10^28, es decir, del orden de **1–3 días** con
2 núcleos y < 1 GB. El coste con X = 10^32 se multiplica por ~100.

**Probabilidad.** ~1 %. Heurísticamente, el número esperado de soluciones en [X, 2X] es ~X^{-1/4},
así que la cola por encima de 10^14 es casi nula. La ventaja es que casi nadie lo está mirando.

---

## Descartados (motivo principal)

| # | estado | motivo |
|---|---|---|
| 19, 475, 551, 556, 580, 742 | decidable | Probados para «n suficientemente grande» con umbral no explícito o astronómico. El resto finito es inabordable. |
| 848 | decidable | Umbral explícito N ≥ 2,64·10^17 (GPT-5.4, foro). El caso finito es un problema de cliques hasta 10^17: inviable. Muy concurrido (48 comentarios, varios equipos con IA). |
| 506 | decidable | Configuraciones de n ≤ 393 puntos del plano: no es una búsqueda finita directa. |
| 647 ($44) | verifiable | Buscado hasta 10^22 con GPU (veljjanoski), con certificados Lean hasta 10^13. Muy concurrido. |
| 7 ($25 / $2000 de Selfridge) | verifiable | Un cubrimiento impar explícito: espacio enorme, 23 comentarios, alguien marcado. P ≈ 0 con 2 núcleos. |
| 835 | verifiable | Ma–Tang dejan solo k = p − 1. Para k = 16 haría falta un *large set* de S(15,16,32). Ya se probó por Kramer–Mesner sin éxito. P ≈ 0. |
| 307 | verifiable | Se reduce a Σ_{p∈P} X/p = ∏Q con \|P∪Q\| ≥ 60 (números de más de 100 cifras que hay que factorizar). Se espera que no haya solución. P ≈ 0. |
| 364, 366, 850, 398, 375, 779, 242 | verifiable/falsifiable | Ya buscados hasta 10^9–10^28 o más. Lo esperado es que no haya ejemplo. |
| 617 | falsifiable | Hay «proof claims» de los casos fijos r = 5, 6, 7, 8 y 9 (varios equipos con IA). El problema general es infinito. |
| 944 | open | Kitamura afirma una prueba en Lean de k = 4, r = 1 (PR #5467 de formal-conjectures). Un ejemplo para r = 2 no cierra todos los r. |
| 114 ($250) | falsifiable | Tao para n grande, con certificados de intervalos hasta n ≤ 14 (con IA). El hueco 15 ≤ n < N_0 no se puede cerrar por cálculo sin un N_0 explícito. |
| 107 ($500) | falsifiable | ES(7): SAT con 33 puntos, del orden de decenas de miles de horas-CPU. Inviable. |
| 411, 1093, 1094, 634 | open | Su resolución no es finita (infinitos casos o «finitely many exceptions»). |

## Recomendación

1. Si el criterio 1 es estricto, mi orden es **#64 > #993 > #128**. Pero aviso de que lo esperable
   es **no** cerrar ninguno: en cada uno se obtendría solo evidencia nueva (más órdenes buscados).
   El primer paso, en cualquier caso, sería una sesión de medida del rendimiento (≤ 1 h de CPU)
   antes de comprometer semanas.
2. Si aceptas relajar el criterio 1 a «cerrar con certificado un caso finito con nombre» (como
   ω = 6 en #470), la probabilidad de éxito sube mucho. Puedo preparar otra ronda de candidatos con
   ese criterio. **No lo he hecho, porque queda fuera del encargo.**
3. No he empezado ninguno. Espero tu elección.

## Fuentes

- `https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml` (2026-11-23).
- Páginas `https://www.erdosproblems.com/N` y `/forum/thread/N` (y `/proof-claims`) de #64, #114,
  #128, #307, #366, #411, #470, #617, #634, #647, #7, #835, #848, #939, #944 y #993, más las 616
  páginas usadas en el cribado. Todas consultadas el 2026-11-23.
- zbMATH Open API (2026-11-23): consultas «unimodal independence polynomial trees» y «coprime
  powerful numbers sum».
- arXiv: consultas propias para #993 y #64 (2026-11-23: 2609.04686, 2608.02675, 2610.22098,
  2603.03025, …). Las demás referencias están citadas desde el foro o desde zbMATH (2510.18826, 2305.01784, 2610.22098, 2603.17114,
  2604.18824, 2606.18462, 2508.08703). Para #128 y #939, la API de arXiv respondió «Rate exceeded» o no
  dio resultados pertinentes, así que **ahí falta una búsqueda independiente en arXiv**. Si eliges uno, es lo primero
  que haría.
