def skewness(data, xbar):
    m3 = sum((x - xbar) ** 3 for x in data) / len(data)
    m2 = sum((x - xbar) ** 2 for x in data) / len(data)
    return m3 / (m2 ** (3 / 2))


def kurtosis(data, xbar):
    m4 = sum((x - xbar) ** 4 for x in data) / len(data)
    m2 = sum((x - xbar) ** 2 for x in data) / len(data)
    return m4 / (m2 ** 2) - 3


def excess_kurtosis(data, xbar):
    return kurtosis(data, xbar) - 3
