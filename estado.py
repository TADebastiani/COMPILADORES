class Estado:
    def __init__(self):
        self.transicoes = []
        self.rotulo = 0
        self.inicial = False
        self.final = False
        self.rotuloGr = ""
        self.alcancaveis = []
        self.eh_token = False
        self.tipo = -1
