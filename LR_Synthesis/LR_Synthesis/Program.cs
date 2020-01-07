using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace LR_Synthesis
{
    // Структура для хранения номеров переходов
    struct TNumber
    {
        public int X; // позиция пункта продукции
        public int Y; // номер продукции
        public string Number; // объединенный номер

        public TNumber(int x, int y)
        {
            X = x;
            Y = y;
            Number = x + "" + y;
        }
    }

    // Класс описывающий состояния LR-автомата
    class State
    {
        public int X; // позиция пункта продукции
        public int Y; // номер продукции
        public string Number; // объединенный номер
        public string Name; // состояние
        public List<string> Transitions; // переходы
        public List<TNumber> TransitionNumbers; // номера переходов

        public State(int x, int y, string name)
        {
            X = x;
            Y = y;
            Name = name;
            Transitions = new List<string>();
            TransitionNumbers = new List<TNumber>();
        }
    }

    static class Program
    {
        static string Expression; // выражение для синтаксического анализа
        static List<string> BaseStates = new List<string>(); // список продукций
        static List<State> States = new List<State>(); // состояния автомата
        static List<string> MarkedArcs; // помеченные переходы
        static Dictionary<string, string> Indexes; //индексы переходов
        static List<string> SortedStates = new List<string>(); // отсортированные состояния
        static List<string> labels = new List<string>(); // метки переходов
        static List<string> Ciphers; // Шифры состояний ДКА
        static List<List<string>> Paths; // Переходы в ДКА для каждого состояния
        static List<string> DKAStates; // Состояния детерминированного LR-автомата
        static Dictionary<string, string> QuasiStates; // Квази состояния

        static void Main(string[] args)
        {
            Init(); // инициализация

            CalculateTransitions(); //расчет переходов

            ShowTransitions(); //отображение переходов

            ConcatXY(); // объединение номеров состояний

            SetMarkedArcsNumbers(); // определение помеченных переходов

            ShowMarkedArcsNumbers(); // отображение помеченных переходов

            Indexes = new Dictionary<string, string>();

            for (int i = 0; i < States.Count; i++)
                for (int j = 0; j < States[i].TransitionNumbers.Count; j++)
                {
                    if (!Indexes.ContainsKey(States[i].TransitionNumbers[j].Number))
                        Indexes.Add(States[i].TransitionNumbers[j].Number, ""); // инициализация словаря индексов состояний
                }

            Indexes["00"] = "1"; // добавление индекса нулевого состояния (начального)

            for (int i = 0; i < States.Count; i++)
                for (int j = 0; j < States[i].TransitionNumbers.Count; j++)
                {
                    SetIndex(States[i].TransitionNumbers[j].Number, States[i].TransitionNumbers[j].Number); // расчет индексов
                }

            ShowLRANtable(); // вывод таблицы синтезированного LR-автомата

            CreateDKAtable(); // составление таблицы ДКА
            ShowDKAtable(); // вывод таблицы детерминированного LR-автомата

            CreateOptimizedDKA(); // более подробный вариант таблицы ДКА (с отображением сверток)
            ShowOptimizedDKAtable(); // вывод данного варианта

            SyntacticAnalysis(); // синтаксический анализ выражения

            Console.ReadLine();
        }

        // Функция чтения входных данных
        static void Init()
        {
            string path = @"C:\Users\Ilya Axenov\source\repos\LR_Synthesis\LR_Synthesis\InputData.txt";
            StreamReader reader = new StreamReader(@path);

            Expression = reader.ReadLine(); // чтение выражения для синтаксического анализа

            int count = Convert.ToInt32(reader.ReadLine()); // чтение количества продукций

            for (int i = 0; i < count; i++)
                BaseStates.Add(reader.ReadLine()); // чтение списка продукций

            reader.Close();
        }

        // Расчет переходов
        static void CalculateTransitions()
        {
            #region Базовые состояния

            // добавление новых состояний
            for (int i = 0; i < BaseStates.Count; i++)
            {
                string Name = BaseStates[i];
                Name = Name.Insert(Name.IndexOf("~") + 1, "#");
                States.Add(new State(0, i, Name)); // добавление продукций поданных на вход
            }

            // добавление переходов
            for (int i = 0; i < BaseStates.Count; i++)
            {
                string BaseTransition = States[i].Name.Insert(States[i].Name.IndexOf("#") + 2, "#");
                BaseTransition = BaseTransition.Remove(BaseTransition.IndexOf("#"), 1); // добавление смещения метасимвола

                States[i].Transitions.Add(BaseTransition); // добавление полученного состояния в список состояний

                for (int j = 0; j < States.Count; j++)
                {
                    if (States[j].Name[0] != BaseTransition[BaseTransition.IndexOf("#") - 1]) // проверка метки по которой делаетя свертка на соответствие рассматриваемому переходу
                        continue;

                    bool IsContains = false;
                    for (int k = 0; k < States[i].Transitions.Count; k++)
                    {
                        if (States[i].Transitions[k].Replace("#", "") == States[j].Name.Replace("#", "")) // проверка наличия просматриваемого перехода в списке переходов
                        {
                            IsContains = true;
                            break;
                        }
                    }

                    if (!IsContains) // при отсутствии перехода
                        States[i].Transitions.Add(States[j].Name); // добавить его в список состояний
                }
            }

            // добавление номеров переходов
            for (int i = 0; i < States.Count; i++)
            {
                for (int j = 0; j < States[i].Transitions.Count; j++)
                {
                    int x = States[i].Transitions[j].IndexOf("#") - 2; // добавление позиции пункта в продукции
                    int y = BaseStates.IndexOf(States[i].Transitions[j].Replace("#", "")); // добавление номера продукции
                    States[i].TransitionNumbers.Add(new TNumber(x, y));
                }
            }

            #endregion

            #region Новые состояния

            string newTransition = "";

            while ((newTransition = IsNewStateExist()) != "")
            {
                // добавление переходов
                string BaseTransition = newTransition.Insert(newTransition.IndexOf("#") + 2, "#");
                BaseTransition = BaseTransition.Remove(BaseTransition.IndexOf("#"), 1); // добавление смещения метасимвола

                States[States.Count - 1].Transitions.Add(BaseTransition); // добавление полученного состояния в список состояний

                for (int j = 0; j < States.Count; j++)
                {
                    if (States[j].Name[0] != BaseTransition[BaseTransition.IndexOf("#") - 1])  // проверка метки по которой делаетя свертка на соответствие рассматриваемому переходу
                        continue;

                    bool IsContains = false;
                    for (int k = 0; k < States[States.Count - 1].Transitions.Count; k++)
                    {
                        if (States[States.Count - 1].Transitions[k].Replace("#", "") == States[j].Name.Replace("#", "")) // проверка наличия просматриваемого перехода в списке переходов
                        {
                            IsContains = true;
                            break;
                        }
                    }

                    if (!IsContains) // при отсутствии перехода
                        States[States.Count - 1].Transitions.Add(States[j].Name); // добавить его в список состояний
                }

                // добавление номеров переходов
                for (int j = 0; j < States[States.Count - 1].Transitions.Count; j++)
                {

                    int x = States[States.Count - 1].Transitions[j].IndexOf("#") - 2;  // добавление позиции пункта в продукции
                    int y = BaseStates.IndexOf(States[States.Count - 1].Transitions[j].Replace("#", "")); // добавление номера продукции
                    States[States.Count - 1].TransitionNumbers.Add(new TNumber(x, y));
                }
            }

            #endregion           

        }

        // Проверка нового состояния на уникальность
        static string IsNewStateExist()
        {
            for (int i = 0; i < States.Count; i++)
            {
                for (int j = 0; j < States[i].Transitions.Count; j++)
                {
                    bool IsUnique = true;
                    for (int k = 0; k < States.Count; k++)
                    {
                        if (States[i].Transitions[j] == States[k].Name) // попарное сравнение данного состояния с уже добавленными
                        {
                            IsUnique = false;
                            break;
                        }
                    }

                    if (IsUnique && States[i].Transitions[j][States[i].Transitions[j].Length - 1] != '#') // если данное состояния уникально и не является конечным
                    {
                        States.Add(new State(States[i].TransitionNumbers[j].X, States[i].TransitionNumbers[j].Y, States[i].Transitions[j])); // добавить его в список состояний

                        return States[i].Transitions[j]; // вернуть номер данного состояния
                    }
                }
            }

            return "";
        }

        // Функция отображения переходов
        static void ShowTransitions()
        {
            for (int i = 0; i < States.Count; i++)
            {
                Console.Write("");
                Console.WriteLine(States[i].X + "" + States[i].Y + "  " + States[i].Name);

                for (int j = 0; j < States[i].Transitions.Count; j++)
                {
                    Console.WriteLine("\t" + States[i].TransitionNumbers[j].X + "" + States[i].TransitionNumbers[j].Y + "  " + States[i].Transitions[j]);
                }
                Console.WriteLine();
            }
        }

        // Объединение позиции пункта продукции и номера продукции в один номер
        static void ConcatXY()
        {
            for (int i = 0; i < States.Count; i++)
            {
                States[i].Number = States[i].X + "" + States[i].Y;
            }
        }

        // Функция возвращающая список состояний, в которые переходит данное состояние
        static string InNodes(string number)
        {
            string inNodes = "";

            for (int i = 0; i < States.Count; i++)
                if (States[i].Number == number) // поиск нужного состояния
                {
                    for (int j = 0; j < States[i].TransitionNumbers.Count; j++)
                        inNodes += States[i].TransitionNumbers[j].Number; // добавление в возвращаемую строку номеров переходных состояний
                }

            if (inNodes != "")
            {
                inNodes = inNodes.Remove(inNodes.Length - 1);
            }

            return inNodes;
        }

        // Функция возвращающая список состояний, которые переходит в данное состояние
        static string OutNodes(string number)
        {
            string outNodes = "";

            for (int i = 0; i < States.Count; i++)
            {
                for (int j = 0; j < States[i].TransitionNumbers.Count; j++)
                    if (States[i].TransitionNumbers[j].Number == number) // поиск состояний у которых есть переход с данным номером
                    {
                        outNodes += States[i].Number + " "; // добавление в возвращаемую строку номеров переходных состояний
                        break;
                    }
            }

            if (outNodes != "")
            {
                outNodes = outNodes.Remove(outNodes.Length - 1);
            }

            return outNodes;
        }

        // Функция определения помеченных вершин
        static void SetMarkedArcsNumbers()
        {
            MarkedArcs = new List<string>(); // инициализация списка помеченных вершин

            MarkedArcs.Add("00 00"); // добавление начальной пустой вершины для смещения индексов

            for (int i = 0; i < States.Count; i++)
            {
                MarkedArcs.Add(States[i].Number + " " + States[i].TransitionNumbers[0].Number + " "); // добавление переходов состояний по непустым меткам
            }
        }

        // Функция вывода помеченных переходов
        static void ShowMarkedArcsNumbers()
        {
            Console.WriteLine("Номера помеченных переходов:");
            for (int i = 1; i < MarkedArcs.Count; i++)
            {
                string[] arcs = MarkedArcs[i].Split('|');

                Console.Write("[" + (i + 1) + "] ");
                foreach (string arc in arcs)
                    Console.Write(arc + "; ");

                Console.WriteLine();
            }

            Console.WriteLine();
        }

        // Функция расчета индексов
        static void SetIndex(string number, string currentNumber, string Path = "")
        {
            Path += currentNumber + " "; // добавлений текущего просматриваемого состояния в список уже просмотренных для избежания зацикливания при просмотре графа

            string[] outNodes = OutNodes(currentNumber).Split(' '); // получение списка состояний, которые переходят в текущее

            if (outNodes.Length == 0 || outNodes.Length == 1 && outNodes[0] == "") // если это начальное состояние "0", то присваивается индекс 1
                if (!Indexes[number].Contains("1"))
                {
                    Indexes[number] += "1";
                    return;
                }

            foreach (string on in outNodes) // просмотр каждого состояния переходящего в данное
            {
                List<int> indexes = new List<int>();

                for (int k = 1; k < MarkedArcs.Count; k++)
                    if (MarkedArcs[k].Contains(on + " " + currentNumber)) // проверка: является просматриваемый переход (из выбранного состояния в текущее) помеченным
                    {
                        indexes.Add(k + 1); // добавление номера такого перехода
                    }

                if (indexes.Count != 0)
                {
                    foreach (int index in indexes)
                    {
                        if (!Indexes[number].Contains(index.ToString()))
                        {
                            if (Indexes[number] != "")
                                Indexes[number] += "," + index.ToString(); // добавление к индексу текущего состояния номера помеченного перехода
                                    else
                                Indexes[number] += index.ToString();
                        }
                    }

                    for (int i = 0; i < indexes.Count; i++)
                    {
                        string arc = MarkedArcs[indexes[i] - 1]; // просмотр перехода из полученного списка индексов

                        string[] a = arc.Split(' ');

                        string label = "";

                        for (int j = 0; j < States.Count; j++)
                        {
                            if (States[j].Number != a[0]) continue;
                            for (int k = 0; k < States[i].TransitionNumbers.Count; k++)
                            {
                                if (States[i].TransitionNumbers[k].Number != a[1]) continue;
                                label = States[i].Transitions[k][States[i].Transitions[k].IndexOf("#") - 1].ToString(); //получение метки просматриваемого перехода
                            }
                        }

                        if (label == "~" && !Path.Contains(on)) // если данная метка пустая, то функция расчета индекса вызывается рекурсивно (если до этого не было вызова функции для данного состояния)
                            SetIndex(number, on, Path);
                    }
                }

                if (indexes.Count == 0 && !Path.Contains(on))
                    SetIndex(number, on, Path); // аналогичный рекурсивный вызов в случае, если для данной метки не было рекурсивного вызова
            }
        }

        // Функция вывода таблицы LR-автомата
        static void ShowLRANtable()
        {
            Console.WriteLine("\n\nТаблица LRAN.");

            labels.Add("@");
            for (int i = 0; i < Expression.Length; i++)
                if (!labels.Contains(Expression[i].ToString()))
                    labels.Add(Expression[i].ToString());
            labels.Add("|");
            labels.Add("A");
            labels.Add("T");

            Console.Write("{0, -14}", "(xy)");
            for (int i = 0; i < labels.Count; i++)
                Console.Write("{0, -14}", labels[i]);
            Console.WriteLine("{0, -14}", "Index");



            // заполнение сортируемого списка
            for (int i = 0; i < States.Count; i++)
            {
                if (!SortedStates.Contains(States[i].Number))
                    SortedStates.Add(States[i].Number);

                for (int j = 0; j < States[i].TransitionNumbers.Count; j++)
                    if (!SortedStates.Contains(States[i].TransitionNumbers[j].Number))
                        SortedStates.Add(States[i].TransitionNumbers[j].Number);
            }

            SortedStates.Sort(); // сортировка состояний для вывода упорядоченного списка

            string[,] Matrix = new string[SortedStates.Count, labels.Count + 2]; // создание матрицы вывода

            for (int i = 0; i < SortedStates.Count; i++)
                for (int j = 0; j < labels.Count + 2; j++)
                    Matrix[i, j] = ""; //инициализация матрицы

            for (int i = 0; i < SortedStates.Count; i++)
            {
                Matrix[i, 0] = SortedStates[i];

                int StateIndex = -1;

                for (int j = 0; j < States.Count; j++)
                {
                    if (SortedStates[i] != States[j].Number) continue;
                    StateIndex = j;
                }

                if (StateIndex != -1)
                {
                    for (int j = 0; j < States[StateIndex].Transitions.Count; j++)
                    {
                        string label = States[StateIndex].Transitions[j][States[StateIndex].Transitions[j].IndexOf("#") - 1].ToString(); // получение метки выбранного перехода

                        if (label == "~")
                        {
                            Matrix[i, 1] += States[StateIndex].TransitionNumbers[j].Number + " "; // установка перехода в матрице для пустой метки
                        }
                        else
                        {
                            int index = labels.IndexOf(label) + 1; // расчет смещения индекса для найденной метки
                            Matrix[i, index] += States[StateIndex].TransitionNumbers[j].Number + " "; // установка перехода в матрице для непустой метки
                        }
                    }
                }

                Matrix[i, labels.Count + 1] = Indexes[SortedStates[i]]; // занесение индексов в последний столбец матрицы
            }

            for (int i = 0; i < SortedStates.Count; i++)
            {
                for (int j = 0; j < labels.Count + 2; j++)
                    Console.Write("{0, -14}", Matrix[i, j]); // вывод построенной матрицы
                Console.WriteLine();
            }
        }

        // Функция отображения таблицы ДКА
        static void ShowDKAtable()
        {
            Console.WriteLine("\n\nТаблица LRAD.");

            Console.Write("{0, -16}", "S");
            Console.Write("{0, -16}", "Шифр");
            Console.Write("{0, -30}", "Состояние");
            foreach (string label in labels)
                Console.Write("{0, -16} ", label);
            Console.WriteLine();

            for (int i = 0; i < Ciphers.Count; i++)
            {
                Console.Write("{0, -16}", (i + 1).ToString()); // вывод порядкового номера
                Console.Write("{0, -16}", Ciphers[i]); // вывод шифра состояния
                Console.Write("{0, -30}", DKAStates[i]); // вывод состояний LRAD

                for (int j = 0; j < labels.Count; j++)
                    Console.Write("{0, -16} ", Paths[i][j]); // вывод переходов

                Console.WriteLine();
            }

            Console.WriteLine();
        }

        // Функция построения ДКА
        static void CreateDKAtable()
        {
            labels.Remove("@"); // удаление пустой метки

            Ciphers = new List<string>(); // инициализация шифров
            Paths = new List<List<string>>(); // инициализация переходов

            SetDKAnode("1", 0);

            List<string> UnrealisedCiphers;

            while ((UnrealisedCiphers = GetUnrealisedCiphers()).Count != 0) // пока присутствуют еще не реализованные шифры, выполнять расчет соответствующих состояний
            {
                foreach (string cipher in UnrealisedCiphers) // просмотр списка нереализованных шифров
                    SetDKAnode(cipher, Ciphers.Count); // расчет очередного шифра
            }

            DKAStates = new List<string>();
            for (int i = 0; i < Ciphers.Count; i ++)
            {
                DKAStates.Add("");

                string[] ciphs = Ciphers[i].Split(','); // разбиение шифров на индексы

                foreach (string c in ciphs) // просмотр полученных индексов
                {
                    for (int j = 0; j < SortedStates.Count; j ++)
                    {
                        string[] indexes = Indexes[SortedStates[j]].Split(','); // получение индекса очередного состояния

                        for (int k = 0; k < indexes.Length; k++)
                            if (indexes[k] == c)
                            {
                                if (DKAStates[i] == "")
                                    DKAStates[i] += SortedStates[j]; // добавление в состояния ДКА индексов удовлетворяющих условию равенства индксам просматриваемого шифра
                                else
                                    DKAStates[i] += "," + SortedStates[j];
                            }
                    }
                }
            }
        }

        // Функция поиска нереализованных шифров
        static List<string> GetUnrealisedCiphers()
        {
            List<string> UnrealisedCiphers = new List<string>(); // инициализация списка новых шифров

            for (int j = 0; j < Ciphers.Count; j++)
                for (int i = 0; i < Paths[0].Count; i++) // просмотр переходов каждого шифра
                {
                    if (!Ciphers.Contains(Paths[j][i]) && Paths[j][i] != "") // если данный переход не реализован как новое состояния, то он добавляется в список
                        UnrealisedCiphers.Add(Paths[j][i]);
                }

            return UnrealisedCiphers;
        }

        // Функция расчета очередного состояния ДКА
        static void SetDKAnode(string cipher, int index)
        {
            Ciphers.Add(cipher); // добавление нового шифра в общий список
            Paths.Add(new List<string>()); // инициализация переходов нового шифра
            for (int i = 0; i < labels.Count; i++)
                Paths[index].Add("");

            for (int j = 0; j < labels.Count; j++) // просмотр каждой метки для заполнения соответствующих переходов
            {
                for (int i = 1; i < MarkedArcs.Count; i++) // просмотр каждого помеченного перехода
                {
                    string[] node = MarkedArcs[i].Split(' '); // разбиение перехода на состояние, из которого начинается переход, и состояние, в котором он заканчивается

                    string label = "";

                    for (int p = 0; p < States.Count; p++)
                    {
                        if (node[0] != States[p].Number) // поиск совпадения номеров переходов исхода
                            continue;
                        for (int l = 0; l < States[p].TransitionNumbers.Count; l++)
                        {
                            if (node[1] != States[p].TransitionNumbers[l].Number) // поиск совпадения номеров переходов перехода
                                continue;
                            label = States[p].Transitions[l][States[p].Transitions[l].IndexOf("#") - 1].ToString(); // получение метки найденного перехода
                            if (label == "~")
                                label = "@";
                        }
                    }


                    if (label == labels[j]) // если метка данного перехода совпадает с текущей рассматриваемой меткой
                    {
                        bool haveIndex = false;

                        string[] ciphers = cipher.Split(','); // разбиение текущего шифра на составляющие его индексы
                        string[] indexes = Indexes[node[0]].Split(','); // получение индекса вершины из текущего перехода

                        for (int h = 0; h < indexes.Length; h++)
                            for (int k = 0; k < ciphers.Length; k++)
                            {
                                if (indexes[h] == ciphers[k]) // поиск совпадения в индексе вершины и просматриваемом шифре
                                {
                                    haveIndex = true;
                                    break;
                                }
                            }

                        if (haveIndex) // если индекс встречается в шифре
                        {
                            if (!Paths[index][j].Contains((i + 1).ToString()))
                            {
                                if (Paths[index][j] != "")
                                    Paths[index][j] += "," + (i + 1).ToString(); // добавление в переход данного состояния номера помеченного перехода
                                else
                                    Paths[index][j] += (i + 1).ToString();
                            }
                        }
                    }
                }
            }
        }

        // Функция построения более подробного варианта таблицы ДКА (с отображением сверток)
        static void CreateOptimizedDKA()
        {
            Dictionary<string, string> UniqueTransitions = new Dictionary<string, string>(); // словарь уникальных переходов

            int count = 2;

            for (int i = 0; i < Paths.Count; i ++)
                for (int j = 0; j < Paths[0].Count; j ++)
                {
                    if (!UniqueTransitions.ContainsKey(Paths[i][j]) && Paths[i][j] != "") // если текущий переход отсутствует в словаре
                    {
                        UniqueTransitions.Add(Paths[i][j], count.ToString()); // добавить данный переход, и его порядковый номер
                        count++; // увеличить счетчик
                    }
                }

            // заполнение таблицы новыми значениями переходов
            for (int i = 0; i < Paths.Count; i++)
                for (int j = 0; j < Paths[0].Count; j++)
                {
                    if (Paths[i][j] != "")
                        Paths[i][j] = UniqueTransitions[Paths[i][j]];
                    else
                        Paths[i][j] = "0"; // установка "0" в пустых переходах
                }
        }

        // Функция вывода данного варианта
        static void ShowOptimizedDKAtable()
        {
            QuasiStates = new Dictionary<string, string>();

            Console.WriteLine("\n\nТаблица LRAD.");

            Console.Write("{0, -16}", "S");
            Console.Write("{0, -30}", "Состояние");
            foreach (string label in labels)
                Console.Write("{0, -16} ", label);
            Console.WriteLine();

            for (int i = 0; i < Ciphers.Count; i++)
            {
                Console.Write("{0, -16}", (i + 1).ToString()); // вывод порядкового номера
                Console.Write("{0, -30}", DKAStates[i]); // вывод состояний LRAD
                bool isPathEmpty = true;
                for (int j = 0; j < labels.Count; j++)
                {
                    if (Paths[i][j] != "0") // определение, является ли данное состояние конечным
                    {
                        isPathEmpty = false;
                        break;
                    }
                }

                if (isPathEmpty) // если это конечное состояние
                {
                    string convolution = "";
                    for (int k = 0; k < States.Count; k ++)
                        for (int j = 0; j < States[k].TransitionNumbers.Count; j ++)
                        {
                            if (States[k].TransitionNumbers[j].Number == DKAStates[i])
                            {
                                convolution = States[k].Transitions[j].Replace("#", ""); // сформировать свертку данного состояния
                                break;
                            }
                        }
                    int number = BaseStates.IndexOf(convolution); // получить номер данной свертки

                    Console.Write("\t\t\t\t\t\t\t\t{0, -16} ", "(" + number + ") " + convolution); // отобразить данную свертку в таблице

                    QuasiStates.Add((i + 1).ToString(), convolution); // добавить конечное состояние в таблицу конечных состояний
                }
                else
                {
                    for (int j = 0; j < labels.Count; j++)
                        Console.Write("{0, -16} ", Paths[i][j]); // вывести переходы для обычных состояний
                }

                Console.WriteLine();
            }

            Console.WriteLine();
        }

        // Синтаксический анализ
        static void SyntacticAnalysis()
        {
            Console.WriteLine("\nСинтаксический анализ\n");

            Stack<string> SS = new Stack<string>(); // Стек состояний
            Stack<string> SC = new Stack<string>(); // Стек символов

            SS.Push(".");
            SC.Push(".");

            string expression = Expression + "|"; // добавление символа конца выражения

            Console.WriteLine("{0, -5} {1, -20} {2, -15} {3, -15} {4, -15}", "№", "Действие", "SS", "SC", "Строка"); // вывод заголовков

            int iteration = 1; //номер итерации
            SS.Push("1");
            SC.Push(expression[0].ToString()); // поместить выражения в строку вывода
            expression = expression.Substring(1); // поместить первый символ строки в стек символов
            Console.WriteLine("{0, -5} {1, -20} {2, -15} {3, -15} {4, -15}", iteration, "__ 1, SC <- i", SS.Content(true), SC.Content(), expression); // вывести начальное состояние


            while (SC.Peek() != "S") // пока на вершине стека символов не окажется один стартовый нетерминал
            {
                iteration++; // увеличить итерацию

                string ssPeek = SS.Peek(); // прочитать символы с вершин стека
                string scPeek = SC.Peek();

                string nextState = Paths[int.Parse(ssPeek) - 1][labels.IndexOf(scPeek)]; // рассчитать состояние по которому будет сделан переход

                if (nextState == "0") // если это нулевое состояния, то завершить работу
                {
                    Console.WriteLine("Состояния ошибки. Завершение работы.");
                    break;
                }
                else if (QuasiStates.ContainsKey(nextState)) // если это квазисостояние
                {
                    string convolution = QuasiStates[nextState]; // получить его свертку

                    string stackPOP = "";
                    int k = 0;

                    while (stackPOP != convolution.Substring(convolution.IndexOf("~") + 1)) // выталкивать из стека символы пока они не образуют нужную последовательность для свертки
                    {
                        stackPOP = SC.Pop() + stackPOP; 
                        k++;
                    }

                    SC.Push(convolution[0].ToString()); // произвести свертку и положить в стек ее результат

                    for (int i = 0; i < k - 1; i++)
                        SS.Pop(); // вытолкнуть из стека состояний k-1 символов

                    Console.WriteLine("{0, -5} {1, -20} {2, -15} {3, -15} {4, -15}", iteration, ssPeek + " " + scPeek + " " + nextState + ", " + convolution, SS.Content(true), SC.Content(), expression); // вывести полученное состояние
                }
                else // если состояние обычное
                {
                    SS.Push(nextState);  // переместить переходное состояние в стек состояний
                    SC.Push(expression[0].ToString()); // переместить первый символ строки в стек символов
                    expression = expression.Substring(1); // удалить перенесенный в стек первый символ строки из строки

                    Console.WriteLine("{0, -5} {1, -20} {2, -15} {3, -15} {4, -15}", iteration, ssPeek + " " + scPeek + " " + nextState + ", " + "SC <- " + SC.Peek(), SS.Content(true), SC.Content(), expression); // вывести полученное состояние
                }
            }
        }

        // Функция получения содержимого стека
        public static string Content(this Stack<string> stack, bool isSS = false)
        {
            string[] arr = stack.ToArray(); // перевод содержимого стека в массив
            arr = arr.Reverse().ToArray(); // изменение порядка следования элементов на обратный
            string ret = ".";
            for (int i = 1; i < arr.Length; i ++)
            {
                ret += arr[i]; // запись элементов в строку
                if (i != arr.Length - 1 && isSS)
                    ret += ",";
            }
            return ret;
        }
    }
}
