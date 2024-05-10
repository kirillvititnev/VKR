import math
import random
import time
import os
graphviz_path = os.path.join(os.path.dirname(os.path.realpath(__file__)),'bin')
os.environ["PATH"]+= os.pathsep + graphviz_path
from graphviz import Digraph


FUNCTION_COMPARATION_ACCURACY_EXP = 4
FUNCTION_COMPARATION_LENGTH = 30
MINIMAL_REPRESENTATION_LENGTH = 100
MINIMAL_COMPARATION_COUNT = 50

def is_prime(number):
    if number <= 1:
        return False
    if number <= 3:
        return True
    if number % 2 == 0 or number % 3 == 0:
        return False
    i = 5
    while i * i <= number:
        if number % i == 0 or number % (i + 2) == 0:
            return False
        i += 6
    return True

# Redefining the gcd function as it seems to have been left out in the previous message
def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

# Redefining the extended Euclidean algorithm to include the gcd function


def p_adic_inverse(s, p, k):
    def extended_euclidean(a, b):
        if a == 0:
            return (b, 0, 1)
        else:
            g, x, y = extended_euclidean(b % a, a)
            return (g, y - (b // a) * x, x)

    g, inv, _ = extended_euclidean(s, p**k)
    if g != 1:
        raise ValueError("Inverse does not exist since gcd ≠ 1")
    return inv % (p**k)

def find_minimal_period(a:tuple):
    for j in range (1, len(a)//3):
        if a[-j:] == a[-2*j:-j] and a[-3*j:-2*j] == a[j:]:
            return a[-j:]
    return None

def to_p_adic(r, s, p):
    common_gcd = gcd(r, s)

    if common_gcd != 1:
        r //= common_gcd
        s //= common_gcd

    if r == 0:
        return (), (0,)

    is_integer = False
    if s == 1:
        is_integer = True

    k = MINIMAL_REPRESENTATION_LENGTH
    s_inv = p_adic_inverse(s, p, k)

    #multiplying r by s^-1 to get  r*s^{-1} mod p^k
    rp = r * s_inv % p**k

    # getting the minimal power of p in canonical representations
    v = 0
    while rp % p == 0 and rp != 0:
        rp //= p
        v += 1

    # getting coefficients in representation
    p_adic_digits = []
    while abs(rp) > 0:
        p_adic_digits.append(rp % p)
        rp //= p

    p_adic_digits = tuple(p_adic_digits)
    if is_integer:
        return (0,)*v+p_adic_digits,""

    #if repreentation if long enought then it contains period and we have to
    #ommit last digits due to rounding errors
    if len(p_adic_digits)>k//2:
        p_adic_digits = p_adic_digits[:-10]

    #getting the period os canonical p-adic representation
    for i in range(len(p_adic_digits)//2, 1, -1):
        if p_adic_digits[-i:] == p_adic_digits[-2*i:-i]:
            p_adic_periodic_part = p_adic_digits[-i:]
            min_per = find_minimal_period(p_adic_periodic_part)
            if min_per == None:
                return (0,)*v + p_adic_digits[:], p_adic_periodic_part
            else:
                return (0,)*v + p_adic_digits[:], find_minimal_period(p_adic_periodic_part)

    return (0,)*v + p_adic_digits[:], ""




#returns p-adic array of result letters with its periods
def fx_rational(x,c,d,e,f,p):
    s, period = to_p_adic(f*c*x+e*d, d*f, p)
    return s, period

#returns array of numbers that correspnds to expansion of function f_{n,k} from Anashin's article
def fnk_rational(n,k,x,c,d,e,f,p):
    tuple1, per1 = fx_rational(n+x*p**k,c,d,e,f,p)
    if len(tuple1) <=2*k:
        while len(tuple1) <= 2*k+1:
            if len(per1) > 0:
                tuple1+=per1
            else:
                tuple1+= (0,)
    return tuple1[k:], per1


#makes a function fingerprint which looks like "f(val1)\nf(val2)...""
def get_function_fingerprint(n,k,c,d,e,f,p):
    res=""
    for x in range(MINIMAL_COMPARATION_COUNT):
        digits, period = fnk_rational(n,k,x,c,d,e,f,p)
        periodic_length = len(period)
        if periodic_length == 0:
            while len(digits)<FUNCTION_COMPARATION_LENGTH:
                digits+=(0,)
        else:
            while len(digits)<FUNCTION_COMPARATION_LENGTH:
                digits+=period
        res+=str(digits[:FUNCTION_COMPARATION_LENGTH])
        res+='\n'
    return res

#возаращает (n,k) для которых функция с таким отпечатком уже встречалась
def compare_fingerprints(current_fingerprint, previous_fingerprints, fingerprint_states):
    for fingerprint in previous_fingerprints:
        if fingerprint == current_fingerprint:
            return fingerprint_states[fingerprint]
    return None

#генерация состояний из текущей вершины графа (n,k)
def generate_states(start_state,c,d,e,f,p):
    previous_fingerprints = set()
    fingerprint_states = dict()
    processing_states = set()
    states=dict()
    got_new_fingerprint = True
    n = start_state[0]
    k = start_state[1]
    processing_states.add(start_state)
    while got_new_fingerprint == True and len(processing_states) != 0:
        got_new_fingerprint == False
        next_processing_states = set()
        for state in processing_states:
            states[state] = dict()
            for input_symbol in range(p):
                states[state][input_symbol] = (fnk_rational(state[0],state[1],input_symbol,c,d,e,f,p)[0][0], (state[0]+input_symbol*p**state[1], state[1]+1))
                next_processing_states.add((state[0]+input_symbol*p**k, state[1]+1))
            current_fingerprint = get_function_fingerprint(state[0],state[1],c,d,e,f,p)
            if compare_fingerprints(current_fingerprint, previous_fingerprints, fingerprint_states) == None:
                fingerprint_states[current_fingerprint] = state
                previous_fingerprints.add(current_fingerprint)
                got_new_fingerprint = True
            else:
                analogical_state = fingerprint_states[current_fingerprint]
                prev_n = state[0]
                prev_k = state[1]-1
                prev_input_symbol = prev_n//(p**(state[1]-1))
                prev_n = int(state[0] - prev_input_symbol * p**(state[1]-1))
                states[(prev_n, prev_k)][prev_input_symbol] = (fnk_rational(prev_n,prev_k,prev_input_symbol,c,d,e,f,p)[0][0], analogical_state)
                for input_symbol in range(p):
                    next_processing_states.remove((state[0]+input_symbol*p**k, state[1]+1))
        processing_states = next_processing_states
        k+=1
    return states



#function that returns reachable states from current state
def search(state_n, state_k, visited, states):
    if (state_n, state_k) in visited:
        return
    visited.add((state_n, state_k))
    for _, (_, next_state) in states[(state_n, state_k)].items():
        search(next_state[0], next_state[1], visited, states)

#finds only reachable states
def reachable_states(states,start_state):
    visited = set()
    search(start_state[0],start_state[1], visited, states)
    return visited

#this function returns map from previous state names (n,k) to simngle decimal i
def change_states_numberation(states, start_state):

    true_numeration = dict()
    true_numeration[(0,0)]=0
    current_state_name = 1
    for state in reachable_states(states, start_state):
        if state == start_state:
            continue
        true_numeration[state] = current_state_name
        current_state_name+=1
    return true_numeration

def create_mealy_diagram(states, final_states, initial_state, c,d,e,f,p, output_file='moore_diagram.gv', file_name="mealy.result.diagram.pv"):
    dot = Digraph(comment='Mealy Machine Diagram', format='png')
    reachable = reachable_states(states, initial_state)
    better_state_names = change_states_numberation(states, initial_state)
    state_label = input("Введите символ для обозначения состояния (например q или s):\n")
    for state_name in states: #создание узлов состояний
        if state_name not in reachable:
            continue

        if state_name == initial_state:
            style = 'filled'
            fillcolor = 'lightblue'
        else:
            style = 'filled' if state_name in final_states else ''
            fillcolor = 'grey' if state_name in final_states else 'white'
        dot.node(f"{state_name[0]},{state_name[1]}", label=state_label+str(better_state_names[state_name]), shape='circle', style=style, fillcolor=fillcolor)

    for state_name, state_rules in states.items(): #создание связей между состояними
        if state_name not in reachable:
            continue
        for input_symbol, (output_symbol, next_state_name) in state_rules.items():
            label = f"{input_symbol}|{output_symbol}"
            dot.edge(f"{state_name[0]},{state_name[1]}", f"{next_state_name[0]},{next_state_name[1]}", label=label)
    output_file=file_name
    dot.render(output_file, view=True)


def reachable_states(states, start_state):
    """
    Returns a set of reachable states from the initial state in the Mealy machine.
    states: A dictionary representing the Mealy machine.
    start_state: The initial state of the Mealy machine.
    """
    reachable = set()
    queue = [start_state]

    while queue:
        current = queue.pop(0)
        if current not in reachable:
            reachable.add(current)
            for _, (_, next_state) in states[current].items():
                queue.append(next_state)

    return reachable

def reachable_states(states, start_state):
    """
    Returns a set of reachable states from the initial state in the Mealy machine.
    states: A dictionary representing the Mealy machine.
    start_state: The initial state of the Mealy machine.
    """
    reachable = set()
    queue = [start_state]

    while queue:
        current = queue.pop(0)
        if current not in reachable:
            reachable.add(current)
            for input_symbol, (_, next_state) in states[current].items():
                if next_state not in reachable:
                    queue.append(next_state)

    return reachable

def moore_from_mealy_states(states, initial_state):
    reachable_mealy_states = reachable_states(states, initial_state)
    moore_states = dict()
    moore_initial_states = set()
    for mealy_state_name, state_transitions in states.items():
        if mealy_state_name not in reachable_mealy_states:
            continue
        if mealy_state_name == initial_state:
            is_initial = True
        for input_symbol, (output_symbol, next_mealy_state_name) in state_transitions.items():
            if (next_mealy_state_name, output_symbol) in moore_states.keys():
                continue
            else:
                moore_states[(next_mealy_state_name, output_symbol)] = ()
            if is_initial:
                moore_initial_states.add((next_mealy_state_name, output_symbol))
    final_moore_states = dict()
    for mealy_state_name, state_transitions in states.items():
        if mealy_state_name not in reachable_mealy_states:
            continue
        for moore_state_name in moore_states.keys():
            if moore_state_name[0] == mealy_state_name:
                for input_sym, (output_symbol, next_mealy_state_name) in state_transitions.items():
                    if moore_state_name not in final_moore_states.keys():
                        final_moore_states[moore_state_name] = dict()
                    final_moore_states[moore_state_name][input_sym] = (next_mealy_state_name, output_symbol)

    state_counter=0
    already_seen = set()
    renamed_moore_states = dict()
    final_renamed = dict()
    for state_name, transitions in final_moore_states.items():

        if state_name not in already_seen:
            renamed_moore_states[f"{state_counter}|{state_name[1]}"] = dict()
            for input_sym, next_state in transitions.items():
                renamed_moore_states[f"{state_counter}|{state_name[1]}"][input_sym] = next_state
                final_renamed[state_name] = f"{state_counter}|{state_name[1]}"
            state_counter+=1


    return renamed_moore_states, moore_initial_states, final_renamed



def create_moore_diagram(states, start_state, filename="moore_diagram"):
    """
    Создает эквивалентный автомат Мура для автомата Мили и визуализирует его.
    states: словарь автомата Мили, где:
        states[state_name][input_symbol] = (output_symbol, next_state)
    start_state: начальное состояние автомата Мили.
    filename: имя файла для сохранения графа (без расширения).
    """
    state_label = input("Введите символ для обозначения состояний (например s или q):\n")
    # Создаем эквивалентный автомат Мура
    Moore_states, state_mapping, renamed_state = moore_from_mealy_states(states, start_state)
    # Создаем граф с помощью graphviz
    dot = Digraph(format="png")
    for state, details in Moore_states.items():
        # Добавляем узлы (состояния)
        label = f"{state_label}{state}"
        if state in state_mapping:
            style = 'filled'
            fillcolor = 'lightblue'
        else:
            style = 'filled'
            fillcolor = 'grey' 
        
        dot.node(state_label+str(state), label=label, style=style, fillcolor=fillcolor)
    for state, details in Moore_states.items():
        # Добавляем переходы
        for input_symbol, next_state in details.items():
            dot.edge(state_label+str(state), state_label+str(renamed_state[next_state]), label=str(input_symbol))
    # Сохраняем граф
    dot.render(filename)
    print(f"Диаграмма мура находится в файле '{filename}.png'")





def simulate_transducer(states, start_state, x:int,c,d,e,f,p):
    true_res, period1 = to_p_adic(c*f*x+e*d, f*d, p)
    x_padic, period2 = to_p_adic(x,1,p)
    currents_state = start_state
    i=0
    output = list()
    is_correct=True
    while len(true_res)<=len(x_padic):
        if len(period1)>0:
            true_res+=period1
        else:
            true_res+=(0,)
    print(f"Проверка корректноси f({x}):")
    for x_i in x_padic:
        if states[currents_state][x_i][0] != true_res[i]:
            is_correct = False
        output.append(states[currents_state][x_i][0])
        currents_state = states[currents_state][x_i][1]
        i+=1
    if is_correct:
        print("Корректно.")
        return
    else:

        print(f"Получена ошибка:\nОжидаемый результат:{true_res}\n, полученный результат:{output}")
        raise ValueError

def test_transducer(states, start_state,c,d,e,f,p):
    while True:
        user_input = input("Чтобы протестировать автомат на 20 псевдослучайных числах из отрезка [0,10^10] введите 'default'.\nЧтобы протестировать программу на заданном целом числе введите 'custom':\n")
        if user_input == 'default':
            for i in range(20):
                x = random.randint(0,10**10+1)
                simulate_transducer(states, start_state, x,c,d,e,f,p)
            break
        elif user_input == 'custom':
            x = int(input("Введите целое число:\n"))
            simulate_transducer(states, start_state, x,c,d,e,f,p)
            break
        else:
            print("Ошибка ввода. Повторите.\n")


def print_states(states):
    print(states)
    print("Состояния автомата:")
    only_reachable = reachable_states(states, (0,0))
    for key, val in states.items():
        if key in only_reachable:
            print("State name:", key)
            print("State transitions and output:", val)
            print()

def run_debug(p):
    for a in range(6):
        for b in range(6):
            for c in range(6):
                for d in range(6):
                    print(a,b,c,d)
                    print(gcd(b,p), gcd(d,p))
                    if (b!=0) and (d!=0) and gcd(b,p)==1 and gcd(d,p)==1:
                        print("doing:")
                        states=generate_states((0,0),c=a,d=b,e=c,f=d,p=p)
                        for x in range(100):
                            simulate_transducer(states, (0,0),x,a,b,c,d,p)
                    else:
                        print("skip")

def main():
    while True:
        states = dict()
        global c,d,e,f
        print("Введите число p.\nЕсли хотите завершить программу введите 'quit':")
        while True:
            user_input = input()
            if user_input.lower() == 'quit':
                return
            try:
                p = int(user_input)
                if is_prime(p):
                    break
            except ValueError:
                print("Число p должно быть простым. Повторите попытку ввода.")
        c = 0
        d = 0
        e = 0
        f = 0
        print("Введите через пробел параметры a,b,c,d для функции f(x)=a*x/b + c/d. \nУчтите, программа работает когда НОД(b,p) = НОД(d,p) = 1\nЧтобы завершить программу напишите 'quit':")
        while True:
            user_input = input()
            if user_input.lower() == 'quit':
                return
            try:
                c,d,e,f = map(int, user_input.split())

                if c!=0:
                    if gcd(d,p)!=1:
                        print("Число b должно быть взаимнопросто с p. Повторите попытку ввода:\n")
                        continue
                if e!=0:
                    if gcd(f,p)!=1:
                        print("Число d должно быть взаимнопросто с p. Повторите попытку ввода:\n")
                        continue
                break
            except ValueError:
                print("Некорректный ввод. Повторите попытку:\n")

        start_state=(0,0)
        print(f"Генерирую состояния автомата для функции f(x)={c}x/{d}+{e}/{f}...")
        try:
            states = generate_states(start_state,c,d,e,f,p)
        except RuntimeError:
            print("Ошибка генерации.")
        create_mealy_diagram(states=states, final_states=set(states.keys()), initial_state=start_state, c=c,d=d,e=e,f=f,p=p)
        while True:
            output_file="result"

            print(f"Состояния сгенерированы. Диаграмма Мура функции f(x)={c}x/{d}+{e}/{f} находится в файле 'mealy.result.diagram.pv'.\nЧтобы вывести состояния на экран введите 'states'.\nЧтобы запустить тестирование поулченного автомата - введите 'test.\nЧтобы вывести состояния и запустить тестирвоание введите 'continue'.\nЧтобы сгенерировать состояния эквивалентного автомата Мура введите 'moore'.\nЧтобы завершить программу введите 'quit':")
            while True:
                user_input = input()
                if user_input == 'quit':
                    break
                elif user_input == 'states':
                    print_states(states)
                    continue
                elif user_input == 'test':
                    start_state = (0,0)
                    test_transducer(states, start_state,c,d,e,f,p)
                    continue
                elif user_input == 'continue':
                    print_states(states)
                    start_state = (0,0)
                    test_transducer(states, start_state,c,d,e,f,p)
                    continue
                elif user_input == 'moore':
                    moore_states = create_moore_diagram(states, start_state)
                    continue
                else:
                    print("Некорректный ввод. Повторите попытку.\n")
                    continue
            want_more = True
            while want_more:
                print("Хотите запустить программу на других данных?\nЕсли да - напишите 'yes', если нет - 'no':\n")
                user_input = input()
                if user_input == "yes":
                    break
                elif user_input == "no":
                    want_more = False
                    break
                else:
                    print("Некорректный ввод. Повторите попытку.\n")
            if want_more:
                break
            else:
                return


