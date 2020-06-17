from PyQt5 import QtCore, QtWidgets, QtSvg
import re
import sys

def svg_file_name(saved_file):
    global file_name
    file_name = saved_file


class Ui_MainWindow(object):
    def setupUi(self, MainWindow):

        max_Width = 850
        max_Height= 850
        print("here2" + file_name)
        with open(file_name, 'r') as myfile:
            data = myfile.read()
        svg_width = re.search('width="(.+?)"', data)
        svg_height = re.search('height="(.+?)"', data)
        if svg_width:
            found_w = svg_width.group(1)
            no_chars_widht = re.sub("[^0-9]", "", found_w)
            int_width = int(no_chars_widht)
        if svg_height:
            found_h = svg_height.group(1)
            no_chars_height = re.sub("[^0-9]", "", found_h)
            int_height = int(no_chars_height)
        ratio_w = max_Width / int_width
        ratio_h = max_Height / int_height
        print(ratio_w)
        print(ratio_h)
        if ratio_w < ratio_h:
            # It must be fixed by width
            resize_width = int_width * ratio_w
            resize_height = round(ratio_w * int_height)
        else:
            # Fixed by height
            resize_width = round(ratio_h * int_width)
            resize_height = int_height * ratio_h

        MainWindow.resize(int(resize_width), int(resize_height))
        MainWindow.setObjectName("MainWindow")

        self.centralwidget = QtWidgets.QWidget(MainWindow)
        self.retranslateUi(MainWindow)
        self.viewer = QtSvg.QSvgWidget()
        self.viewer.load(file_name)

        lay = QtWidgets.QVBoxLayout(self.centralwidget)
        lay.addWidget(self.viewer)
        MainWindow.setCentralWidget(self.centralwidget)
        # ...

    def retranslateUi(self, MainWindow):
        _translate = QtCore.QCoreApplication.translate
        MainWindow.setWindowTitle(_translate("MainWindow", "MainWindow"))


def run():
    app = QtWidgets.QApplication(sys.argv)
    MainWindow = QtWidgets.QMainWindow()
    ui = Ui_MainWindow()
    ui.setupUi(MainWindow)
    MainWindow.show()
    app.exec_()


