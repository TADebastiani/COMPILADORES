from estado import Estado
from transicao import Transicao


class AFND:
    def __init__(self, arquivo):
        self._count_estado = 0
        self._count_gramatica = 0
        self.estados = []
        self.alfabeto = []

        for linha in arquivo:
            if linha[len(linha) - 1] != '\n':
                linha = linha + '\n'
            if not self.estados:
                est = Estado()
                est.rotulo = self._count_estado
                est.inicial = True
                est.rotuloGr = 'S'
                self.estados.append(est)
                self._count_estado += 1
            elif linha[0] == '<' and linha[1] != '=' and linha[1] != '\n':
                self._le_gramatica(linha)
            # else:
            #     le_token(linha)

    def _add_estado(self, rotulo):
        estado = Estado()
        estado.rotulo = self._count_estado
        estado.rotuloGr = rotulo
        self.estados.append(estado)
        self._count_estado += 1
        return estado

    # Recebe como parametro uma linha da entrada referente a um Estado e suas produçoes
    # converte essa linha em estados no AFD
    def _le_gramatica(self, linha):
        i_linha = 1

        rotulo, i_linha = _le_rotulo_estado(linha, i_linha)

        if rotulo == 'S':
            self._count_gramatica += 1

        estado_existe = False
        for estado in self.estados:
            if estado.rotuloGr == rotulo:
                estado_existe = True
                break

        if not estado_existe:
            self._add_estado(rotulo)

        while linha[i_linha] != '\n':
            while linha[i_linha] == '>' or \
                    linha[i_linha] == ' ' or \
                    linha[i_linha] == ':' or \
                    linha[i_linha] == '=' or \
                    linha[i_linha] == '|':
                i_linha += 1
            if linha[i_linha] == '\n':
                break
            term = linha[i_linha]
            if term not in self.alfabeto and term != 'ε':
                self.alfabeto.append(term)
            i_linha += 1

            if linha[i_linha] == '<':
                i_linha += 1
                nao_term, i_linha = _le_rotulo_estado(linha, i_linha)
                i_linha += 1
                self._nao_terminal(rotulo, term, nao_term)

            else:
                if term == 'ε':
                    for estado in self.estados:
                        if estado.rotuloGr == rotulo:
                            estado.final = True
                            if self._count_gramatica > 1:
                                estado.tipo = 1
                            else:
                                estado.tipo = 0
                self._terminal(rotulo, term)

    # Recebe como parametro o estado, o terminal e o nao terminal da producao
    # Cria o estado ou a transicao no AF caso necessário
    # Caso em que a produção contem um terminal e um não terminal ex: a<A>
    def _nao_terminal(self, estado, terminal, nao_term):
        flag = False
        tem_nao_term = False
        indice = 0
        rotulo = 0

        for est in self.estados:
            if est.rotuloGr != estado:
                indice += 1
            if est.rotuloGr == nao_term:
                tem_nao_term = True
                rotulo = est.rotulo

        for prox_estado in self.estados[indice].transicoes:
            if prox_estado.rotulo == terminal:
                flag = True
                if tem_nao_term:
                    if rotulo not in prox_estado.transicoes:
                        prox_estado.transicoes.append(rotulo)
                else:
                    prox_estado.transicoes.append(self._count_estado)
                    self._add_estado(nao_term)
                break

        if not flag:
            transicao = Transicao()
            transicao.rotulo = terminal
            if tem_nao_term:
                transicao.transicoes.append(rotulo)
            else:
                transicao.transicoes.append(self._count_estado)
                self._add_estado(nao_term)
            self.estados[indice].transicoes.append(transicao)

    # Recebe como parametro o estado e o terminal da producao
    # Cria a transicao no AF caso necessário
    # Caso em que a produção contem apenas o terminal ex: ε
    def _terminal(self, estado, terminal):
        indice = 0
        flag = False
        for est in self.estados:
            if est.rotuloGr == estado:
                break
            indice += 1

        for prox_estado in self.estados[indice].transicoes:
            if prox_estado.rotulo == terminal:
                flag = True
                prox_estado.transicoes.append(self._count_estado)

        if not flag:
            transicao = Transicao()
            transicao.rotulo = terminal
            transicao.transicoes.append(self._count_estado)

        est = self._add_estado("")
        est.final = True


# Lê o estado entre os símbolos "<" e ">"
def _le_rotulo_estado(linha, i):
    rotulo = ""
    while linha[i] != '>':
        rotulo = rotulo + linha[i]
        i += 1
    return rotulo, i

