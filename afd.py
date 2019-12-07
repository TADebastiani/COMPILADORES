from estado import Estado
from transicao import Transicao


class AFD:
    def __init__(self, afnd):
        self.alfabeto = afnd.alfabeto
        self.estados = []
        self._determiniza(afnd)

    def _determiniza(self, afnd):
        count = 0
        fila = []
        fila_aux = []
        lista = [afnd.estados[0].rotulo]
        fila.append(lista)
        fila_aux.append(lista)
        while fila:
            estado = Estado()
            estado.rotulo = count
            count += 1
            for j in self.alfabeto:
                cont = 0
                transicao = Transicao()
                transicao.rotulo = j
                for i in fila[0]:
                    estado.final = afnd.estados[i].final
                    estado.inicial = afnd.estados[i].inicial
                    estado.eh_token = afnd.estados[i].eh_token
                    if not afnd.estados[i].eh_token:
                        if afnd.estados[i].tipo == 0:
                            estado.tipo = 0
                        else:
                            estado.tipo = 1
                    for k in afnd.estados[i].transicoes:
                        if k.rotulo == j:
                            for l in k.transicoes:
                                if l not in transicao.transicoes:
                                    transicao.transicoes.append(l)
                                    transicao.transicoes.sort()
                if transicao.transicoes not in fila_aux:
                    if transicao.transicoes:
                        fila.append(transicao.transicoes)
                        fila_aux.append(transicao.transicoes)
                for c in fila_aux:
                    if c == transicao.transicoes:
                        transicao.trans = cont
                    cont += 1
                estado.transicoes.append(transicao)
            self.estados.append(estado)
            fila.pop(0)
