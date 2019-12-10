# Refatoração do código feito por: Tiago Debastiani e Ricardo Muller
#
# Academicos: Gabriel Rudey, Jefferson Coppini, Jonathan Rauber, Nicholas Brutti e Ricardo Muller
# Trabalho 2
# Disciplina: Compiladores
import csv

from SimboloSintatico import *
from erro import Erro
from estado import Estado
from goldpyser import *
from nodo import Nodo
from prettytable import PrettyTable
from token import Token
from transicao import *

# erros
ERRO_LEX = 0
ERRO_SINTATICO = 1

# GLOBAIS
TABELA_ERROS = []
TABELA_SIMBOLOS = []
AFND = []
ALFABETO = []
CONT_ESTADO = 0
I_LINHA = 0
ESTADOS = []
AFD = []
FITA = []
i = 0
CONT_LINHA = 1
TABELA_SLR = []
PRODS = []
CODI = []
CONTNODO = 0
CONT_TEMP = 0
TABELA_SIMBOLOS_SINTATICA = []
CONT_GRAMM = 0


# Lê o estado entre os símbolos "<" e ">"
def split_nt(linha):
    global I_LINHA
    nt = ""

    while linha[I_LINHA] != '>':
        nt = nt + linha[I_LINHA]
        I_LINHA += 1
    return nt


# Recebe como parametro uma linha da entrada referente a um token
# converte esse token em estados no AF
def le_token(linha):
    global AFND, ALFABETO, CONT_ESTADO
    flag = 0
    for i in AFND[0].transicoes:
        if i.rotulo == linha[0]:
            i.transicoes.append(CONT_ESTADO)
            flag = 1

    if flag == 0:
        transic = Transicao()
        transic.rotulo = linha[0]
        transic.transicoes.append(CONT_ESTADO)
        AFND[0].transicoes.append(transic)

    if linha[0] not in ALFABETO and linha[0] != 'ε':
        ALFABETO.append(linha[0])

    i = 1

    while linha[i] != '\n':
        estad = Estado()
        estad.rotulo = CONT_ESTADO
        CONT_ESTADO += 1
        trans = Transicao()
        trans.rotulo = linha[i]
        trans.transicoes.append(CONT_ESTADO)
        estad.transicoes.append(trans)
        AFND.append(estad)
        if linha[i] not in ALFABETO and linha[0] != 'ε':
            ALFABETO.append(linha[i])
        i += 1

    estad = Estado()
    estad.rotulo = CONT_ESTADO
    estad.final = True
    estad.eh_token = True
    CONT_ESTADO += 1
    AFND.append(estad)


# Recebe como parametro o estado, o terminal e o nao terminal da producao
# Cria o estado ou a transicao no AF caso necessário
# Caso em que a produção contem um terminal e um não terminal ex: a<A>
def nao_terminal(estad, term, nao_term):
    global AFND, CONT_ESTADO, ALFABETO, ESTADOS
    flag = 0
    have_nao_term = False
    cont = 0
    rot = 0
    for i in ESTADOS:
        if i.rotuloGr == estad:
            break
        cont += 1

    for i in ESTADOS:
        if i.rotuloGr == nao_term:
            have_nao_term = True
            rot = i.rotulo

    for i in ESTADOS[cont].transicoes:
        if i.rotulo == term:
            flag = 1
            if have_nao_term:
                if rot not in i.transicoes:
                    i.transicoes.append(rot)
            else:
                i.transicoes.append(CONT_ESTADO)
                est = Estado()
                est.rotulo = CONT_ESTADO
                est.rotuloGr = nao_term
                CONT_ESTADO += 1
                ESTADOS.append(est)
                AFND.append(est)
            break

    if flag == 0:
        transi = Transicao()
        transi.rotulo = term
        if have_nao_term:
            transi.transicoes.append(rot)
        else:
            transi.transicoes.append(CONT_ESTADO)
            est = Estado()
            est.rotulo = CONT_ESTADO
            est.rotuloGr = nao_term
            CONT_ESTADO += 1
            ESTADOS.append(est)
            AFND.append(est)
        ESTADOS[cont].transicoes.append(transi)


# Recebe como parametro o estado e o terminal da producao
# Cria a transicao no AF caso necessário
# Caso em que a produção contem apenas o terminal ex: ε
def terminal(estad, term):
    global AFND, CONT_ESTADO, ALFABETO, ESTADOS

    cont = 0
    flag = 0
    for i in ESTADOS:
        if i.rotuloGr == estad:
            break
        cont += 1

    for i in ESTADOS[cont].transicoes:
        if i.rotulo == term:
            flag = 1
            i.transicoes.append(CONT_ESTADO)

    if flag == 0:
        transi = Transicao()
        transi.rotulo = term
        transi.transicoes.append(CONT_ESTADO)
        ESTADOS[cont].transicoes.append(transi)
    est = Estado()
    est.final = True
    est.rotulo = CONT_ESTADO
    CONT_ESTADO += 1
    ESTADOS.append(est)
    AFND.append(est)


# Inicializa o vetor de estados, para controle na criação de estados com mesmo nome em gramaticas diferentes
def inicializa_estado():
    global ESTADOS, AFND
    while ESTADOS:
        ESTADOS.pop(0)
    ESTADOS.append(AFND[0])


# Recebe como parametro uma linha da entrada referente a um Estado e suas produçoes
# converte essa linha em estados no AFD
def le_gramatica(linha):
    global AFND, CONT_ESTADO, ALFABETO, I_LINHA, ESTADOS, CONT_GRAMM
    I_LINHA = 1

    std = split_nt(linha)
    if std == 'S':
        inicializa_estado()
        CONT_GRAMM += 1

    flag = 0
    for i in ESTADOS:
        if i.rotuloGr == std:
            flag = 1

    if flag == 0:
        est = Estado()
        est.rotulo = CONT_ESTADO
        est.rotuloGr = std
        CONT_ESTADO += 1
        ESTADOS.append(est)
        AFND.append(est)

    while linha[I_LINHA] != '\n':
        while linha[I_LINHA] == '>' or linha[I_LINHA] == ' ' or linha[I_LINHA] == ':' or linha[I_LINHA] == '=' or \
                linha[I_LINHA] == '|':
            I_LINHA += 1
        if linha[I_LINHA] == '\n':
            break
        term = linha[I_LINHA]
        if term not in ALFABETO and term != 'ε':
            ALFABETO.append(term)
        I_LINHA += 1

        if linha[I_LINHA] == '<':
            I_LINHA += 1
            nao_term = split_nt(linha)
            I_LINHA += 1
            nao_terminal(std, term, nao_term)

        else:
            if term == 'ε':
                for i in ESTADOS:
                    if i.rotuloGr == std:
                        i.final = True
                        if CONT_GRAMM > 1:
                            i.tipo = 1
                        else:
                            i.tipo = 0
            terminal(std, term)


# Imprime na tela automato nao deterministico
def print_ident_afnd():
    header = ['δ'] + ALFABETO
    t = PrettyTable(header)
    for i in AFND:
        linha = []
        linha = [i.rotulo]
        if i.final:
            linha = ['*' + str(i.rotulo)]
        else:
            linha = [i.rotulo]
        for k in ALFABETO:
            flag = 0
            for j in i.transicoes:
                if j.rotulo == k:
                    linha = linha + [j.transicoes]
                    flag = 1
            if flag == 0:
                linha = linha + ['X']
        t.add_row(linha)
    print(t)


# Imprime na tela automato deterministico
def print_ident_afd(comErro=False):
    header = ['δ'] + ALFABETO
    if comErro:
        header = header + ['x']
    t = PrettyTable(header)
    for i in AFD:
        if i.final:
            linha = ['*' + str(i.rotulo)]
        else:
            linha = [i.rotulo]
        for j in i.transicoes:
            if j.trans != -1:
                linha = linha + [j.trans]
            else:
                linha = linha + ['X']
        t.add_row(linha)
    print(t)


# função que determiniza o AFND
# cria o AFD
# Costroi o AFD a partir do estado inicial
# Por ser construído a partir de seu estado inicial a função elimina os estados inalcançaveis
def determinizar():
    global AFND, AFD, CONT_ESTADO
    CONTADOR = 0
    fila = []
    fila_aux = []
    lista = []
    lista.append(AFND[0].rotulo)
    fila.append(lista)
    fila_aux.append(lista)
    while fila:
        est = Estado()
        est.rotulo = CONTADOR
        CONTADOR += 1
        for j in ALFABETO:
            cont = 0
            trans = Transicao()
            trans.rotulo = j
            for i in fila[0]:
                if AFND[i].final:
                    est.final = True
                if AFND[i].inicial:
                    est.inicial = True
                if AFND[i].eh_token:
                    est.eh_token = True
                if not AFND[i].eh_token:
                    if AFND[i].tipo == 0:
                        est.tipo = 0
                    else:
                        est.tipo = 1
                for k in AFND[i].transicoes:
                    if k.rotulo == j:
                        for l in k.transicoes:
                            if l not in trans.transicoes:
                                trans.transicoes.append(l)
                                trans.transicoes.sort()
            if trans.transicoes not in fila_aux:
                if trans.transicoes:
                    fila.append(trans.transicoes)
                    fila_aux.append(trans.transicoes)
            for c in fila_aux:
                if c == trans.transicoes:
                    trans.trans = cont
                cont += 1
            est.transicoes.append(trans)
        AFD.append(est)
        fila.pop(0)


# adiciona ao atributo alcancaveis de cada estado, os estados que podem ser alcançaveis a partir dele mesmo
# utilizado para verificação dos estados mortos
def alcancaveis():
    global AFD
    change = True

    for i in AFD:
        if i.rotulo not in i.alcancaveis:
            i.alcancaveis.append(i.rotulo)
        for j in i.transicoes:
            if j.trans not in i.alcancaveis:
                if j.trans != -1:
                    i.alcancaveis.append(j.trans)
    while change:
        change = False
        for i in AFD:
            for j in i.alcancaveis:
                for k in AFD[j].alcancaveis:
                    if k not in i.alcancaveis:
                        i.alcancaveis.append(k)
                        i.alcancaveis.sort()
                        change = True


# Exclui do AFD o estado que não chega a algum estado final
# verifica em cada estado o vetor de alcancaveis, se nenhum deles for final o estado é eliminado
def mortos():
    global AFD
    mortos = []
    alcancaveis()

    for i in AFD:
        have_final = False
        for j in i.alcancaveis:
            if AFD[j].final:
                have_final = True
        if not have_final:
            mortos.append(i.rotulo)
            for k in AFD:
                cont = 0
                for j in k.transicoes:
                    if j.trans == i.rotulo:
                        j.trans = -1
    for i in mortos:
        cont = 0
        for j in AFD:
            if i == j.rotulo:
                AFD.pop(cont)
            cont += 1


# insere estado de erro após automato ser minimizado
def insere_estado_erro():
    global AFD

    est = Estado()
    est.rotulo = len(AFD)
    est.rotuloGr = 'X'
    est.final = True
    AFD.append(est)
    for _ in ALFABETO:
        trans = Transicao()
        trans.trans = est.rotulo
        est.transicoes.append(trans)

    for i in AFD:
        for j in i.transicoes:
            if j.trans == -1:
                j.trans = est.rotulo
    for i in AFD:
        trans = Transicao()
        trans.trans = est.rotulo
        i.transicoes.append(trans)


# gera arquivo csv do AFD
def gerar_csv():
    global AFD

    alf = ["Estado"]

    for i in ALFABETO:
        alf.append(i)

    f = open('AFD.csv', 'w')
    writer = csv.writer(f)

    writer.writerow(alf)
    for i in AFD:
        linha = [i.rotulo]
        for j in i.transicoes:
            linha.append(j.trans)
        writer.writerow(linha)


# funçao que recebe uma linha como parametro
# retorna um token
def split_token2(linha):
    global i
    token = ""
    while linha[i] == ' ' or linha[i] == '\t':
        i += 1
    if ((linha[i] == '<' and linha[i + 1] == '=') or (linha[i] == '>' and linha[i + 1] == '=') or (
            linha[i] == '!' and linha[i + 1] == '=') or (linha[i] == '=' and linha[i + 1] == '=') or (
            linha[i] == '&' and linha[i + 1] == '&') or (linha[i] == '|' and linha[i + 1] == '|')):
        token = linha[i] + linha[i + 1] + '\n'
        i += 2
        while linha[i] == ' ':
            i += 1
        return token

    if (linha[i] == '+' or linha[i] == '-' or linha[i] == '/' or linha[i] == '*' or linha[i] == '%' or linha[
        i] == '(' or linha[i] == ')' or linha[i] == '{' or linha[i] == '}' or linha[i] == '>' or linha[i] == '<' or
            linha[i] == ';' or linha[i] == '='):
        token = linha[i] + '\n'
        i += 1
        while linha[i] == ' ':
            i += 1
        return token
    else:
        while (linha[i] not in [' ', '\n', '+', '-', '*', '/', ';', '%', '>', '<', '=', '!', '(', ')', '{', '}', '&',
                                '|']):
            token = token + linha[i]
            i += 1
        while linha[i] == ' ':
            i += 1
        token = token + '\n'
        return token


# funçao que recebe uma linha como parametro
# retorna um token
def split_token(linha):
    global i
    token = ""
    while linha[i] != " " and linha[i] != '\n':
        token = token + linha[i]
        i += 1
    while linha[i] == ' ':
        i += 1
    token = token + '\n'
    return token


# a funçao recebe como parametro um codigo, um rotulo, um atributo e um tipo
# insere token na tabela de simbolos
def insere_var(cod, toke, eh_token, tipo):
    global TABELA_SIMBOLOS
    tok = Token()
    tok.cod = cod
    tok.token = toke
    tok.eh_token = eh_token
    tok.linha = CONT_LINHA
    tok.tipo = tipo
    TABELA_SIMBOLOS.append(tok)


# funcao recebe como parametro um token
# verifica se o teken eh reconheceido no AFD
# retorna True se positivo
# caso contrario False
def rec_token(token):
    global AFD, FITA
    i = 0
    rot = 0
    aux = 0
    flag = 0
    while token[i] != '\n':
        flag = 0
        for j in AFD[rot].transicoes:
            if j.rotulo == token[i]:
                flag = 1
                if token[i + 1] == '\n' and AFD[j.trans].final and AFD[j.trans].rotuloGr != 'X':
                    FITA.append(j.trans)
                    insere_var(j.trans, token, AFD[j.trans].eh_token, AFD[j.trans].tipo)
                    return True
                else:
                    aux = j.trans

        if flag == 0:
            return False
        rot = aux
        i += 1
    return False


# Faz a analise lexica do codigo fonte
# retorna verdadeiro caso a analise lexica ocorra com sucesso
# retorna falso caso contrario
def lexic():
    global i, CONT_LINHA
    sucesso = True
    with open("fonte.txt", "r") as arquivo:
        for linha in arquivo:
            i = 0
            while linha[i] != '\n':
                token = split_token2(linha)
                rec = rec_token(token)
                if not rec:
                    er = Erro()
                    er.token = token
                    er.cod_erro = ERRO_LEX
                    er.linha = CONT_LINHA
                    TABELA_ERROS.append(er)
                    sucesso = False
            CONT_LINHA += 1
    return sucesso


# Recebe como parametro uma flag que significa se ocorreu erro ou nao
# e um variavel tipo que identifica se eh erro lexico ou sintatico
# imprime Tabela de erros
def print_erros(flag, tipo):
    global TABELA_ERROS
    if flag:
        if tipo == ERRO_LEX:
            print()
            print("Análise léxica não contém erros!")
            print()
        else:
            print("Análise sintática não contém erros!")
            print()
    else:
        print("------TABELA DE ERROS------")
        print()
        for i in TABELA_ERROS:
            if i.cod_erro == 0:
                print("Erro na análise léxica!! Linha:" + str(i.linha) + " Token:" + str(i.token))
            if i.cod_erro == 1:
                print("Erro na análise sintática!! Linha:" + str(i.linha) + " Token:" + str(i.token))
        print()


# Imprime tabela de simbolos da etapa de analise sintatica
def print_tabela_simbolos_sintaticos():
    global TABELA_SIMBOLOS_SINTATICA
    print("------TABELA DE SÍMBOLOS------")
    print()
    for i in TABELA_SIMBOLOS_SINTATICA:
        print("Rótulo = " + i.rotulo + " Valor = " + i.val, " Tipo = " + i.tipo)
    print()


# imprime tabela de simbolos da etapa de analise lexica
def print_tabela_simbolos():
    print("------TABELA DE SÍMBOLOS------")
    print()
    for i in TABELA_SIMBOLOS:
        if i.eh_token == True:
            tipo = "TOKEN"
            print("Cod: {} Tipo: {} Token: {}".format(i.cod, tipo, i.token), end='')
        else:
            if i.tipo == 0:
                tipo = "VARIÁVEL"
                print("Cod: {} Tipo: {} Token: {}".format(i.cod, tipo, i.token), end='')
            if i.tipo == 1:
                tipo = "NUMERAL"
                print("Cod: {} Tipo: {} Token: {}".format(i.cod, tipo, i.token), end='')
    print()


# imprime tabela LSR
def print_tabela_slr(tabela_slr):
    for i in tabela_slr:
        print(i.rotulo, end=" === ")
        for j in i.transicoes:
            print(j, end="")
        print()


# funcao que recebe como parametro a reducao, os caracteres da fita e o codigo temporario da reduçao
# realiza operaçoes de açoes semanticas em produçoes
# retorna o codigo temporario da reducao
def acao_semantica(r, caracs, cod):
    global CONT_TEMP, TABELA_SIMBOLOS_SINTATICA

    if r == 35 or r == 39 or r == 41 or r == 40:  # adiciona à pilha
        cod.append(caracs[len(caracs) - 1])

    if r == 28 or r == 29 or r == 31 or r == 32:  # cria um temporário com a operação
        temp = "temp" + str(CONT_TEMP)
        CODI.append(temp + " = " + cod[len(cod) - 2] + " " + caracs[1] + " " + cod[len(cod) - 1])
        cod.pop(len(cod) - 1)
        cod.pop(len(cod) - 1)
        cod.append(temp)
        CONT_TEMP += 1

    if r == 25:  # final de produção
        simbolo = SimboloSintatico()
        simbolo.rotulo = caracs[len(caracs) - 1]
        simbolo.val = cod[len(cod) - 1]
        simbolo.tipo = "oper"
        TABELA_SIMBOLOS_SINTATICA.append(simbolo)

    if r == 38:  # declaração de variável - atribui o tipo
        CODI.append(cod[len(cod) - 1] + " " + caracs[1])
        simbolo = SimboloSintatico()
        simbolo.rotulo = caracs[1]
        simbolo.val = cod[len(cod) - 1]
        simbolo.tipo = "var"
        TABELA_SIMBOLOS_SINTATICA.append(simbolo)
        cod.pop(len(cod) - 1)

    if r == 26:  # atribuição entre duas variáveis
        CODI.append(caracs[3] + " = " + caracs[1])
        simbolo = SimboloSintatico()
        simbolo.val = caracs[1]
        simbolo.rotulo = caracs[3]
        simbolo.tipo = "atrib"
        TABELA_SIMBOLOS_SINTATICA.append(simbolo)
    return cod


# Faz a analise sintatica do codigo
# retorna verdadeiro caso a analise sintatica ocorra com sucesso
# retorna falso caso contrario
def analise_sintatica():
    global TABELA_SIMBOLOS
    cod = []
    tabela_slr = read_from_xml("grammar.xml")

    prods = get_productions_from_xml("grammar.xml")
    pilha = ['0']
    indice = 0
    reconhece = True
    aceita = False
    LINHA = 0
    ERRO = ""
    while reconhece and not aceita:
        if indice != len(TABELA_SIMBOLOS):
            LINHA = TABELA_SIMBOLOS[indice].linha
            pos_fita = TABELA_SIMBOLOS[indice].token
            pos_fita = pos_fita[:-1]
            token = TABELA_SIMBOLOS[indice].eh_token
        else:
            token = True
            pos_fita = "EOF"

        pos_pilha = int(pilha[len(pilha) - 1])
        op = " "
        pos_fita2 = " "

        if not token:
            pos_fita2 = "var"
        else:
            pos_fita2 = pos_fita

        for i in tabela_slr:
            if i.rotulo == pos_fita2:
                op = i.transicoes[pos_pilha]

        tipo = op[:1]
        if tipo == 'X':
            ERRO = pos_fita
            reconhece = False

        elif tipo == 'T':
            t = op[1:]
            pilha.append(pos_fita)
            pilha.append(t)
            indice += 1

        elif tipo == 'R':
            r = int(op[1:])
            tam = 2 * int(prods[r].tam)
            nt = int(prods[r].regra)
            caracs = []

            while tam > 0:
                if tam % 2 == 1:
                    caracs.append(pilha[len(pilha) - 1])
                pilha.pop(len(pilha) - 1)
                tam -= 1
            cod = acao_semantica(r, caracs, cod)
            pos = int(pilha[len(pilha) - 1])
            salto = tabela_slr[nt].transicoes[pos]
            pilha.append(str(tabela_slr[nt].rotulo))
            pilha.append(str(salto))

        elif tipo == 'A':
            aceita = True

    if not aceita:
        er = Erro()
        er.linha = LINHA
        er.token = ERRO
        er.cod_erro = ERRO_SINTATICO
        TABELA_ERROS.append(er)
        print_erros(False, ERRO_SINTATICO)
    else:
        print_tabela_simbolos_sintaticos()
        print_erros(True, ERRO_SINTATICO)
    return aceita


# funcao que recebe como parametro uma linha do codigo intemediario e um grafo
# Gera nodos dessa linha no grafo
def gera_nodos(lin, grafo):
    global CONTNODO
    at1 = True
    at2 = True
    rot1 = 0
    rot2 = 0
    lin[4] = lin[4][:-1]
    nodo1 = None
    nodo2 = None

    for i in grafo:
        if i.var == lin[2]:
            rot1 = i.pos
            at1 = False
        if i.var == lin[4]:
            rot2 = i.pos
            at2 = False

    if at1:
        nodo1 = Nodo()
        nodo1.pos = CONTNODO
        nodo1.var = lin[2]
        CONTNODO += 1
        grafo.append(nodo1)

    if at2:
        nodo2 = Nodo()
        nodo2.pos = CONTNODO
        nodo2.var = lin[4]
        CONTNODO += 1
        grafo.append(nodo2)

    nodotemp = Nodo()
    nodotemp.pos = CONTNODO
    nodotemp.var = lin[0]
    nodotemp.op = lin[3]
    if at1:
        nodotemp.filhos.append(nodo1.pos)
    else:
        nodotemp.filhos.append(rot1)
    if at2:
        nodotemp.filhos.append(nodo2.pos)
    else:
        nodotemp.filhos.append(rot2)
    grafo[nodotemp.filhos[0]].pai.append(CONTNODO)
    grafo[nodotemp.filhos[1]].pai.append(CONTNODO)
    CONTNODO += 1
    grafo.append(nodotemp)


# funcao que recebe como parametro um grafo e uma lista de nodos
# percorre o grafo em profundidade mais a esquerda
# fundamental para o processo de otimizaçao
def dfs(grafo, ordemInst):
    pilha = [ordemInst[len(ordemInst) - 1]]
    ar = False
    on = False
    while pilha:
        for aresta in pilha[len(pilha) - 1].filhos:
            if grafo[aresta] not in ordemInst and grafo[aresta].filhos:
                for pai in grafo[aresta].pai:
                    if grafo[pai] in ordemInst:
                        on = True
                    else:
                        on = False
                        break
                if on:
                    ordemInst.append(grafo[aresta])
                    pilha.append(grafo[aresta])
                    ar = True
                    break
        if not ar:
            pilha.pop(len(pilha) - 1)
        on = False
        ar = False


# funçao recebe como parametro um grafo e uma pilha
# escreve o codigo otimizado no arquivo codOtimizado.txt
def codigo_otimizado(ordemInst, grafo):
    arquivo = open('codOtimizado.txt', 'a')
    k = len(ordemInst) - 1
    while k >= 0:
        i = ordemInst[k]
        arquivo.write(
            str(i.var) + " = " + grafo[i.filhos[0]].var + " " + i.op + " " + grafo[i.filhos[1]].var + " " + "\n")
        k -= 1
    arquivo.close()


# funcao que realiza a otimizaçao do codigo intermediario
def otimizacao():
    grafo = []
    ordemInst = []

    with open("codIntermediario.txt", "r") as arquivo:
        for linha in arquivo:
            linha.strip('\n')
            lin = linha.split(" ")
            if len(lin) == 5:
                gera_nodos(lin, grafo)
            else:
                arquivo = open('codOtimizado.txt', 'a')
                arquivo.write(str(linha))
                arquivo.close()

    for nodo in grafo:
        if len(nodo.pai) == 0 and nodo not in ordemInst:
            ordemInst.append(nodo)
            dfs(grafo, ordemInst)
    codigo_otimizado(ordemInst, grafo)


# funcao que escrece o codigo intermediario gerado na analise sintatica no arquivo codIntermediario.txt
def gera_codigo_intermediario():
    arquivo = open('codIntermediario.txt', 'w')
    for i in CODI:
        arquivo.write(i + '\n')
    arquivo.close()


# Faz a analise semantica recorrente da analise sintatica
# Apenas para o caso  de var = var
def analise_semantica():
    val1 = ""
    val2 = ""
    eh_var = False
    for i in TABELA_SIMBOLOS_SINTATICA:
        if i.tipo == "atrib":
            for j in TABELA_SIMBOLOS_SINTATICA:
                if j.tipo == "var":
                    if i.rotulo == j.rotulo:
                        val1 = j.val
            for k in TABELA_SIMBOLOS_SINTATICA:
                if k.tipo == "var":
                    if i.val == k.rotulo:
                        eh_var = True
                        val2 = k.val
            if val1 != val2 and eh_var:
                print(
                    "erro semantico na expressão: " + i.rotulo + "(" + val1 + ")" + " = " + "" + i.val + "(" + val2 + ")")
                print()
            eh_var = False


def main():
    global CONT_ESTADO, AFND, ESTADOS, CONT_LINHA
    # abre o arquivo em modo de leitura
    arquivo = open('codOtimizado.txt', 'w')
    arquivo.write(str(""))
    arquivo.close()

    with open("entrada.txt", "r") as arquivo:
        for linha in arquivo:
            if linha[len(linha) - 1] != '\n':
                linha = linha + '\n'
            if not AFND:
                est = Estado()
                est.rotulo = CONT_ESTADO
                est.inicial = True
                est.rotuloGr = 'S'
                AFND.append(est)
                CONT_ESTADO += 1
            elif linha[0] == '<' and linha[1] != '=' and linha[1] != '\n':
                le_gramatica(linha)
            else:
                le_token(linha)
        determinizar()
        mortos()
        insere_estado_erro()
        gerar_csv()
        print_erros(lexic(), ERRO_LEX)
        print_tabela_simbolos()
        if not TABELA_ERROS:
            aceita = analise_sintatica()
            if aceita:
                analise_semantica()
                gera_codigo_intermediario()
                otimizacao()


main()
