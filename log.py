import logging

#formatter = logging.Formatter('[%(filename)s:%(lineno)d] %(funcName)s %(levelname)s - %(message)s','%m-%d %H:%M:%S')
formatter = logging.Formatter('%(message)s','%m-%d %H:%M:%S')
handler = logging.StreamHandler()
handler.setFormatter(formatter)

#Choisir le niveau de log
handler.setLevel(logging.DEBUG)
# handler.setLevel(logging.INFO)
#
logger = logging.getLogger()
logger.setLevel(logging.INFO)
if not logger.handlers:
    logger.addHandler(handler)
