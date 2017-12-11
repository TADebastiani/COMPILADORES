class Production():
    def __init__(self, tam, regra):
        self.tam = tam
        self.regra = regra

    def __str__(self):
        return "{} => {}".format(self.regra, self.tam)
