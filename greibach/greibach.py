# Christiano Braga
# Nov. 2020
# Grammar transformation to Greibach normal form.
# The productios of a grammar are represented as a dictionary where
# each item is a set of RHS productions with the same LHS. The key is the
# LHS and the value is a list, whose elements are each RHS of the given
# LHS in the production set.

# Given a grammar G = (V, T, P, S), all symbols are strings, V is
# implemented as a list and so is T. S is a string and P is as
# described above.

import pprint
from termcolor import colored
import copy
import itertools

def sort_variables(v):
    v_set = set(v)
    v_list = list(v_set)
    return v_list

def r_lte_s(v, p_0):
    p = copy.deepcopy(p_0)
    for a_r in v:
        for a_s in v: 
            if v.index(a_s) < v.index(a_r):
                rhs_list = p[a_r]
                for rhs in rhs_list:
                    if rhs[0] == a_s:
                        for beta in p[a_s]:
                            beta_copy = beta.copy()
                            beta_copy.extend(rhs[1:]) # beta alpha
                            p[a_r].append(beta_copy)
                        p[a_r].remove(rhs)
    return p

def left_recursion_elimination(v, p_0):
    p = copy.deepcopy(p_0)
    excluded = []
    new_p = {}
    for a_r in p:
        for i, rhs in enumerate(p[a_r]):
            if rhs[0] == a_r:
                rhs_copy = rhs.copy()
                b_r = rhs_copy[0] + "_rr"
                v = v.append(b_r)
                alpha = rhs_copy[1:]
                alpha_x = alpha.copy()
                alpha_x.append(b_r)
                new_p.update({ b_r : [alpha, alpha_x] })
                p[a_r].remove(rhs)
                excluded += a_r
    p.update(new_p)
    for a_r in excluded:
        rhs_list = copy.deepcopy(p[a_r])
        for rhs in rhs_list:
            rhs_copy = rhs.copy()
            rhs_copy.append(a_r + "_rr")
            p[a_r].append(rhs_copy)
    return p

# Foi adicionado à função um novo parâmetro "v" para manter a ordem das variáveis, dado que como "p" é um dicionário,
# ao tentar recuperar as chaves de "p", a ordem nem sempre era compatível com a ordem em "v"
def begin_with_terminal(v, p):
    
    # Encontra a posição em em v onde começam as variáveis auxiliares
    i = 0
    while not v[i].endswith("_rr"): i += 1

    # a_keys: lista de variáveis iniciais
    # b_keys: lista de variáveis auxiliares
    a_keys, b_keys = v[:i], v[i:]

    # Percorre variáveis "A" da penúltima para a primeira
    for a_r in reversed(a_keys[:-1]):
        
        # Variável depois de a_r
        a_s = a_keys[ a_keys.index(a_r)+1 ]
        
        # Produções de a_r
        rhs_list = p[a_r].copy()

        for rhs in rhs_list:
            if rhs[0] == a_s:
                for beta in p[a_s]:
                    beta_copy = beta.copy()
                    beta_copy.extend(rhs[1:])
                    p[a_r].append(beta_copy)

                p[a_r].remove(rhs)

    # Percorre as variáveis auxiliares "B"
    for b in b_keys:

        # Produções de b
        rhs_list = p[b].copy()

        for rhs in rhs_list:
            if rhs[0] in a_keys:
                for beta in p[rhs[0]]:
                    beta_copy = beta.copy()
                    beta_copy.extend(rhs[1:])
                    p[b].append(beta_copy)
                p[b].remove(rhs)

    return p

# Foi adicionado à função um novo parâmetro "v", com o mesmo objetivo do método anterior
def terminal_followed_by_word_of_variables(v, p):

    # Produções auxiliares que poderão ser geradas
    new_p = {}

    for a_r in v:

        rhs_list = p[a_r].copy()
        for rhs in rhs_list:

            # Percorre os itens da produção (do 2º até o último)
            for i in range(1, len(rhs)):

                # Se rhs[i] não é uma variável
                if rhs[i] not in v:
                    new_v = None

                    # Verifica se produção já está em new_p
                    for k, k_list in new_p.items():
                        if rhs[i] in k_list:
                            new_v = k
                    
                    # Se não está em new_p, cria nova variável auxiliar
                    if not new_v:
                        new_v = "X_" + str(len(new_p) + 1)
                        new_p[new_v] = [rhs[i]]
                    
                    # Substitui o terminal pela nova variável
                    rhs[i] = new_v

            # Atualiza as produções com as novas váriaveis no lugar dos terminais
            p[a_r] = rhs_list

    # Adiciona as variáveis auxiliares às produções
    p.update(new_p)

    return p

def print_prod(p):
    for key in p.keys():
        print(colored(key, 'magenta') + colored(" → ", 'white', attrs=['bold']) + colored(" ".join(p[key][0]), 'cyan'))
        for rhs in p[key][1:]:
            print(colored(" | ", 'white', attrs=['bold']) + colored(" ".join(rhs), 'cyan'))
    
def mk_example(ex_num, v_0, p_0):
    pp = pprint.PrettyPrinter(indent=4)
    print(colored("Example " + str(ex_num), attrs=['bold']))
    print("Original production set.")
    print_prod(p_0)
    
    for i, v in enumerate(list(itertools.permutations(v_0))):
        print(colored("Example "+ str(ex_num) + "." + str(i), 'green', attrs=['bold']))
        
        # First step: grammar simplification
        print(colored("Second step: sort variables", 'blue'))
        v = list(v)
        pp.pprint(v)

        # Third and fourth steps: production set transformation to
        # A_r → A_s α, where r ≤ s and removal of productions of the form
        # Ar → Arα.
        
        print(colored("Production set transformation to A_r → A_s α, where r ≤ s.", 'blue'))
        p_i = r_lte_s(v, p_0)
        print_prod(p_i)
        print(colored("Production set elimination of A_r → A_r α.", 'blue'))    
        p_i = left_recursion_elimination(v, p_i)
        print_prod(p_i)
        print(colored("Each production begining with a terminal.", 'blue'))
        p_i = begin_with_terminal(v, p_i)
        print_prod(p_i)
        print(colored("Each production begining with a terminal followed by a word of variables.", 'blue'))
        p_i = terminal_followed_by_word_of_variables(v, p_i)
        print_prod(p_i)
    
if __name__ == "__main__":
    print(colored("Examples of transformations from CFG to Greibach normal form", attrs=['bold']))

    ### Example 1
    v_0 = ["A", "S"]
    t = ["a", "b"]
    p_0 = { "S" : [["A", "A"], ["a"]], "A" : [["S", "S"], ["b"]] }
    s  = "S"
    mk_example(1, v_0, p_0)

    ### Example 2
    v1 = ["A", "B", "C"]
    t1 = ["a", "b"]
    p1 = { "A" : [["B", "C"]], "B" : [["C", "A"], ["b"]], "C" : [["A", "B"], ["a"]] }
    s1  = "A"
    mk_example(2, v1, p1)
    
