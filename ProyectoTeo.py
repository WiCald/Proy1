from collections import defaultdict, deque
from graphviz import Digraph

# Precedencia de operadores
PRECEDENCIA = {'*': 3, '.': 2, '|': 1}

# Convertir infix a postfix usando el algoritmo Shunting Yard
# Precedencia de operadores
PRECEDENCIA = {'*': 3, '.': 2, '|': 1}

# Convertir infix a postfix usando el algoritmo Shunting Yard
def infix_a_postfix(expresion):
    salida = []
    pila = []
    for caracter in expresion:
        if caracter.isalnum():  # Si es un operando (a, b, etc.)
            salida.append(caracter)
        elif caracter == '(':  # Paréntesis izquierdo
            pila.append(caracter)
        elif caracter == ')':  # Paréntesis derecho
            while pila and pila[-1] != '(':
                salida.append(pila.pop())
            pila.pop()  # Eliminar '('
        else:  # Operador
            while pila and pila[-1] != '(' and PRECEDENCIA.get(caracter, 0) <= PRECEDENCIA.get(pila[-1], 0):
                salida.append(pila.pop())
            pila.append(caracter)  # Agregar el operador a la pila
    while pila:
        salida.append(pila.pop())  # Vaciar la pila restante
    return ''.join(salida)

# Implementación de Thompson para construir un AFN
class Estado:
    def __init__(self, id):
        self.id = id
        self.transiciones = defaultdict(list)

class AFN:
    def __init__(self, estado_inicial, estado_aceptacion):
        self.estado_inicial = estado_inicial
        self.estado_aceptacion = estado_aceptacion
        self.estados = {estado_inicial, estado_aceptacion}

    def agregar_transicion(self, desde, simbolo, hacia):
        desde.transiciones[simbolo].append(hacia)
        self.estados.add(desde)
        self.estados.add(hacia)

def thompson(postfix):
    stack = []
    estado_id = 0

    def nuevo_estado():
        nonlocal estado_id
        estado_id += 1
        return Estado(estado_id)

    for simbolo in postfix:
        if simbolo.isalnum():  # Operando
            e1 = nuevo_estado()
            e2 = nuevo_estado()
            e1.transiciones[simbolo].append(e2)
            afn = AFN(e1, e2)
            stack.append(afn)
        elif simbolo == '*':  # Cierre de Kleene
            afn = stack.pop()
            e1 = nuevo_estado()
            e2 = nuevo_estado()
            # Añadir transiciones epsilon para el ciclo del cierre de Kleene
            e1.transiciones['ε'].append(afn.estado_inicial)
            e1.transiciones['ε'].append(e2)
            afn.estado_aceptacion.transiciones['ε'].append(afn.estado_inicial)
            afn.estado_aceptacion.transiciones['ε'].append(e2)
            nuevo_afn = AFN(e1, e2)
            stack.append(nuevo_afn)
        elif simbolo == '|':  # Alternancia (ab|bc)
            afn2 = stack.pop()
            afn1 = stack.pop()
            e1 = nuevo_estado()
            e2 = nuevo_estado()
            # Añadir transiciones epsilon para gestionar las opciones
            e1.transiciones['ε'].append(afn1.estado_inicial)
            e1.transiciones['ε'].append(afn2.estado_inicial)
            afn1.estado_aceptacion.transiciones['ε'].append(e2)
            afn2.estado_aceptacion.transiciones['ε'].append(e2)
            nuevo_afn = AFN(e1, e2)
            stack.append(nuevo_afn)
        elif simbolo == '.':  # Concatenación
            afn2 = stack.pop()
            afn1 = stack.pop()
            # Concatenar uniendo el estado de aceptación del primero al inicial del segundo
            afn1.estado_aceptacion.transiciones['ε'].append(afn2.estado_inicial)
            nuevo_afn = AFN(afn1.estado_inicial, afn2.estado_aceptacion)
            stack.append(nuevo_afn)

    return stack.pop()

# Construcción de AFD mediante subconjuntos
class AFD:
    def __init__(self, estados, transiciones, estado_inicial, estados_aceptacion):
        self.estados = estados
        self.transiciones = transiciones
        self.estado_inicial = estado_inicial
        self.estados_aceptacion = estados_aceptacion

def mover(estados, simbolo):
    resultado = set()
    for estado in estados:
        if simbolo in estado.transiciones:
            resultado.update(estado.transiciones[simbolo])
    return resultado

def cerradura_epsilon(estados):
    """ Calcula la cerradura epsilon de un conjunto de estados """
    stack = list(estados)
    cerradura = set(estados)
    while stack:
        estado = stack.pop()
        for siguiente in estado.transiciones.get('ε', []):
            if siguiente not in cerradura:
                cerradura.add(siguiente)
                stack.append(siguiente)
    return cerradura

def subconjuntos(afn):
    estado_id = 0
    def nuevo_estado():
        nonlocal estado_id
        estado_id += 1
        return estado_id

    dfa_estados = {}
    dfa_transiciones = {}
    estado_inicial = frozenset(cerradura_epsilon([afn.estado_inicial]))
    dfa_estados[estado_inicial] = nuevo_estado()

    pendientes = [estado_inicial]
    procesados = set()
    estados_aceptacion = set()

    while pendientes:
        t = pendientes.pop()
        procesados.add(t)

        for simbolo in {simbolo for estado in t for simbolo in estado.transiciones if simbolo != 'ε'}:
            mover_resultado = mover(t, simbolo)
            u = frozenset(cerradura_epsilon(mover_resultado))

            if u not in dfa_estados:
                dfa_estados[u] = nuevo_estado()
                pendientes.append(u)

            dfa_transiciones[(dfa_estados[t], simbolo)] = dfa_estados[u]

        if afn.estado_aceptacion in t:
            estados_aceptacion.add(dfa_estados[t])

    return AFD(dfa_estados, dfa_transiciones, dfa_estados[estado_inicial], estados_aceptacion)

# Minimización de AFD usando particiones
def minimizar_afd(afd):
    P = [afd.estados_aceptacion, set(afd.estados) - set(afd.estados_aceptacion)]
    W = deque([afd.estados_aceptacion, set(afd.estados) - set(afd.estados_aceptacion)])

    while W:
        A = W.popleft()
        for simbolo in {simbolo for (estado, simbolo) in afd.transiciones}:
            X = {estado for estado in afd.estados if (estado, simbolo) in afd.transiciones and afd.transiciones[(estado, simbolo)] in A}
            nuevas_particiones = []
            for Y in P:
                interseccion = Y & X
                diferencia = Y - X
                if interseccion and diferencia:
                    P.remove(Y)
                    P.append(interseccion)
                    P.append(diferencia)
                    if Y in W:
                        W.remove(Y)
                        W.append(interseccion)
                        W.append(diferencia)
                    else:
                        W.append(interseccion if len(interseccion) <= len(diferencia) else diferencia)

    # Actualización: Construir el nuevo AFD minimizado
    estado_id_map = {}
    for idx, particion in enumerate(P):
        for estado in particion:
            estado_id_map[estado] = idx  # Asignamos el nuevo ID al estado

    afd_min_transiciones = {}
    for (estado, simbolo), destino in afd.transiciones.items():
        nuevo_origen = estado_id_map.get(estado)
        nuevo_destino = estado_id_map.get(destino)
        if nuevo_origen is not None and nuevo_destino is not None:
            afd_min_transiciones[(nuevo_origen, simbolo)] = nuevo_destino

    nuevo_estado_inicial = estado_id_map.get(afd.estado_inicial)
    nuevos_estados_aceptacion = {estado_id_map[estado] for estado in afd.estados_aceptacion if estado in estado_id_map}

    return AFD(set(estado_id_map.values()), afd_min_transiciones, nuevo_estado_inicial, nuevos_estados_aceptacion)

def simular_afn(afn, cadena):
    """ Simula el AFN sobre una cadena dada """
    actuales = cerradura_epsilon([afn.estado_inicial])
    print(f"Estados iniciales (cerradura-epsilon): {[estado.id for estado in actuales]}")

    for simbolo in cadena:
        siguientes = set()
        for estado in actuales:
            print(f"Procesando desde el estado {estado.id} con el símbolo {simbolo}")
            if simbolo in estado.transiciones:
                siguientes.update(estado.transiciones[simbolo])  # Transición normal por el símbolo
            else:
                print(f"No hay transición definida para el símbolo {simbolo} desde el estado {estado.id}")

        if not siguientes:
            print("No hay estados activos, la cadena no es aceptada.")
            return False

        actuales = cerradura_epsilon(siguientes)
        print(f"Estados actuales después de procesar {simbolo}: {[estado.id for estado in actuales]}")

    # Verificar si el estado de aceptación está en los estados actuales
    resultado = afn.estado_aceptacion in actuales
    print(f"Resultado final AFN: {'sí' if resultado else 'no'}")
    return resultado

# Simulación de AFD
def simular_afd(afd, cadena):
    estado_actual = afd.estado_inicial
    for simbolo in cadena:
        estado_actual = afd.transiciones.get((estado_actual, simbolo))
        if estado_actual is None:
            return False
    return estado_actual in afd.estados_aceptacion

# Generar gráfico para un AF (AFN o AFD)
def generar_grafico(af, nombre_archivo, es_afn=True):
    dot = Digraph()
    
    if es_afn:
        # Graficar AFN
        for estado in af.estados:
            shape = "doublecircle" if estado == af.estado_aceptacion else "circle"
            dot.node(str(estado.id), shape=shape)
            for simbolo, siguientes in estado.transiciones.items():
                for siguiente in siguientes:
                    dot.edge(str(estado.id), str(siguiente.id), label=simbolo)
    else:
        # Graficar AFD o AFD minimizado
        for estado in af.estados:
            shape = "doublecircle" if estado in af.estados_aceptacion else "circle"
            
            if isinstance(estado, frozenset):
                estado_str = ','.join(map(str, [s.id for s in estado]))  # Convertir a string de IDs
            else:
                estado_str = str(estado)

            dot.node(estado_str, shape=shape)

            for (origen, simbolo), destino in af.transiciones.items():
                if isinstance(origen, frozenset):
                    origen_str = ','.join(map(str, [s.id for s in origen]))  # Convertir a string de IDs
                else:
                    origen_str = str(origen)

                if isinstance(destino, frozenset):
                    destino_str = ','.join(map(str, [s.id for s in destino]))  # Convertir a string de IDs
                else:
                    destino_str = str(destino)

                dot.edge(origen_str, destino_str, label=simbolo)

    dot.render(nombre_archivo, format='png')

# Función principal para procesar el archivo
def procesar_archivo(nombre_archivo):
    with open(nombre_archivo, 'r', encoding='utf-8') as archivo:
        for linea in archivo:
            linea = linea.strip()
            
            # Verificar si la línea contiene una coma (para el caso de expresión y cadena)
            if ',' in linea:
                expresion_regular, cadena = linea.split(',')
                expresion_regular = expresion_regular.strip()  # Eliminar espacios en blanco de la expresión regular
                cadena = cadena.strip()  # Eliminar espacios en blanco de la cadena
                print(f"Procesando: r = {expresion_regular}, w = {cadena}")
            else:
                # Caso donde solo hay una expresión regular
                expresion_regular = linea.strip()
                cadena = ""  # Asignar cadena vacía si no hay cadena proporcionada
                print(f"Procesando: r = {expresion_regular}")

            # Convertir la expresión regular a postfix
            postfix = infix_a_postfix(expresion_regular)
            print(f"Postfix: {postfix}")
            
            # Construir el AFN con Thompson
            afn = thompson(postfix)
            generar_grafico(afn, 'afn_grafo', es_afn=True)
            
            # Convertir AFN a AFD
            afd = subconjuntos(afn)
            generar_grafico(afd, 'afd_grafo', es_afn=False)
            
            # Minimizar el AFD
            afd_min = minimizar_afd(afd)
            generar_grafico(afd_min, 'afd_min_grafo', es_afn=False)
            
            # Simulación del AFN
            resultado_afn = simular_afn(afn, cadena)
            # Simulación del AFD minimizado
            resultado_afd = simular_afd(afd_min, cadena)
            
            # Mostrar los resultados
            print(f"Resultado AFN: {'sí' if resultado_afn else 'no'}")
            print(f"Resultado AFD: {'sí' if resultado_afd else 'no'}")

if __name__ == '__main__':
    procesar_archivo('expresiones_regulares.txt')
