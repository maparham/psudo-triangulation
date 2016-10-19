#include <CGAL/basic.h>
#include <CGAL/intersections.h>
#include <CGAL/Exact_predicates_exact_constructions_kernel.h>
#include <CGAL/number_utils.h>
#include <iostream>
#include <boost/format.hpp>
#include <QtGui>
#include <QBitmap>
#include <CGAL/Qt/GraphicsViewNavigation.h>
#include <CGAL/Cartesian.h>
#include <CGAL/Arr_segment_traits_2.h>
#include <CGAL/Point_2.h>
#include <CGAL/Line_2.h>
#include <CGAL/Arr_extended_dcel.h>
#include <CGAL/Arrangement_2.h>
#include <CGAL/convex_hull_2.h>
#include <CGAL/spatial_sort.h>
#include <qbrush.h>
#include <CGAL/Qt/DemosMainWindow.h>
#include <CGAL/Qt/PainterOstream.h>
#include <CGAL/Qt/GraphicsItem.h>
#include<CGAL/Arr_naive_point_location.h>
#include<CGAL/Arrangement_on_surface_2.h>
#include <qpainter.h>

enum Color {
    BLUE, RED, WHITE
};

typedef CGAL::Cartesian<double> Kernel;
typedef CGAL::Arr_segment_traits_2<Kernel> Traits_2;
typedef CGAL::Point_2<Kernel> Point;
typedef CGAL::Segment_2<Kernel> Segment;
typedef CGAL::Arr_extended_dcel<Traits_2, Color, bool, int> Dcel;
typedef CGAL::Arrangement_2<Traits_2, Dcel> Arrangement_2;
typedef Arrangement_2::Vertex_handle Vertex_handle;
typedef Arrangement_2::Vertex_const_handle Vertex_const_handle;
typedef Arrangement_2::Halfedge_handle Halfedge_handle;
typedef Arrangement_2::Vertex vertex;
typedef std::vector<Point> PointList;
typedef std::vector<Vertex_handle> VHList;
typedef CGAL::Line_2<Kernel> Line;
typedef CGAL::Arr_naive_point_location<Arrangement_2> PointLocation;
typedef PointLocation::Vertex_const_handle v_h;

bool enablePrune = true;

void write(PointList points) {
    for (int i = 0; i < points.size(); i++) {

        Point p = points[i];
        std::cout << p << '\n';
    }
}

bool getHalfedge(Vertex_handle source_h, Vertex_handle target_h, Arrangement_2 &arr, Halfedge_handle &he) {

    PointLocation::Arrangement_2::Halfedge_around_vertex_const_circulator first, curr;
    if (target_h->is_isolated()) return false;
    first = curr = target_h->incident_halfedges();
    do {
        if (curr->source()->point() == source_h->point()) {
            he = arr.non_const_handle(curr);
            return true;
        }
        ++curr;

    } while (curr != first);

    return false;
}

bool getHalfedge(Point p1, Point p2, Arrangement_2 &arr, Halfedge_handle &he) {

    PointLocation pl(arr);
    Vertex_const_handle vh1, vh2;

    CGAL::Object obj = pl.locate(p1);

    if (CGAL::assign(vh1, obj)) {

        obj = pl.locate(p2);
        if (CGAL::assign(vh2, obj)) {
            if (vh2->is_isolated()) return false;
            Arrangement_2::Halfedge_around_vertex_const_circulator first, curr;
            first = curr = vh2->incident_halfedges();
            do {
                //                                std::cout << "check ---->>>" << curr->source()->point() << "==" << vh1->point() << std::endl;
                if (curr->source()->point() == vh1->point()) {
                    he = arr.non_const_handle(curr);
                    return true;
                }
                ++curr;
            } while (curr != first);
        }
    }

    return false;
}

void splitPoints(PointList points, Point middle, PointList &left, PointList &right) {

    std::sort(points.begin(), points.end());

    int i;
    for (i = 0; i < points.size() && points[i] != middle; i++) {
        Point p = points[i];
        //        std::cout << "=====>>>>>>>>>>>>>>>>>>>>>>>>>> p=" << p << ", middle=" << middle << std::endl;
        left.push_back(p);
    }
    for (; i < points.size(); i++) {
        Point p = points[i];
        right.push_back(p);
    }
    left.push_back(middle); //middle should be in both sides
}

Point getMiddle(PointList points) {

    std::sort(points.begin(), points.end());
    int m = (points.size() / 2);
    return points[m];
}

void addToDCEL(Arrangement_2 &arr, PointList boundry, VHList &vh_boundry) {

    std::cout << "==>> inserting convex hull edges to the Arrangement (addToDCEL)..." << std::endl;
    Halfedge_handle e1;

    for (int i = 0; i < boundry.size(); i++) { // insert boundry of CH in CCW order starting from v1
        Point p1 = boundry[i];
        Point p2 = boundry[(i + 1) % boundry.size()];

        //check whether (p1,p2) has been created before

        if (getHalfedge(p1, p2, arr, e1)) {
            std::cout << "exists >>" << " source=" << e1->source()->point() << " target=" << e1->target()->point() << "\n";
            vh_boundry.push_back(e1->target()); //insert v(i+1)
            continue;
        }

        Vertex_handle src;
        Vertex_handle tar;
        Segment s(p1, p2);

        PointLocation pl(arr);
        CGAL::Object obj1 = pl.locate(p1);
        CGAL::Object obj2 = pl.locate(p2);
        Vertex_const_handle x1, x2;
        bool b1 = CGAL::assign(x1, obj1);
        bool b2 = CGAL::assign(x2, obj2);

        if (b1 && b2) {
            std::cout << "b1 && b2 ";
            src = arr.non_const_handle(x1);
            tar = arr.non_const_handle(x2);

            //            std::cout << "isolated=" << src->is_isolated() << " point=" << src->point() << std::endl;
            //            std::cout << "isolated=" << tar->is_isolated() << " point=" << tar->point() << std::endl;

            e1 = arr.insert_at_vertices(s, src, tar);

        } else if (b1 && !b2) {
            std::cout << "b1 && !b2 ";
            src = arr.non_const_handle(x1);

            if (p1.x() <= p2.x()) {

                e1 = arr.insert_from_left_vertex(s, src);

            } else {
                e1 = arr.insert_from_right_vertex(s, src);
            }

        } else if (!b1 && b2) {
            std::cout << "!b1 && b2 ";
            tar = arr.non_const_handle(x2);
            //            std::cout << "isolated=" <<tar->is_isolated() << " point=" <<tar->point() << std::endl;

            if (p1.x() <= p2.x()) {
                e1 = arr.insert_from_right_vertex(s, tar);
                //                std::cout << "xxxxxxxxxxxxxxxxx   >>" << " source=" << e1->source()->point() << " target=" << e1->target()->point() << std::endl;

            } else {
                e1 = arr.insert_from_left_vertex(s, tar);
                //                std::cout << "yyyyyyyyyyyyyyyyy   >>" << " source=" << e1->source()->point() << " target=" << e1->target()->point() << std::endl;
            }

        } else if (!b1 && !b2) {

            std::cout << "!b1 && !b2 ";
            e1 = arr.insert_in_face_interior(s, arr.unbounded_face());
            //            std::cout << "isolated=" << e1->source()->is_isolated() << " point=" << e1->source()->point() << std::endl;
            //            std::cout << "isolated=" << e1->target()->is_isolated() << " point=" << e1->target()->point() << std::endl;

        }

        vh_boundry.push_back(e1->target()); //insert v(i+1)
        std::cout << "created>>" << " source=" << e1->source()->point() << " target=" << e1->target()->point() << "\n";

        Halfedge_handle hh;
        //        std::cout << "gethalfedge (p2,p1)=" << getHalfedge(p2, p1, arr, hh) << std::endl;
        //        std::cout << "gethalfedge (p1,p2)=" << getHalfedge(p1, p2, arr, hh) << std::endl;
        arr.is_valid();


    }//for

    std::cout << "nubmer of faces>> " << arr.number_of_faces() << "\n";
}

bool decide(VHList v_boundry, PointList candidates) {

    std::cout << "==>> examine vertex degrees to decide on prune or partition... \n";
    bool partition = true;

    for (int i = 0; i < v_boundry.size(); i++) {
        Vertex_handle vh = v_boundry[i];

        if (vh->degree() > 3) {
            //a vertex with degree greater than 3 is a candidate for pruning
            partition = false;
            candidates.push_back(vh->point());

        } else if (vh->degree() == 3) { 
            //save candidates for pruning. 
            candidates.push_back(vh->point());
        }
    }//for
    return partition;
}

void ST(PointList points, PointList ch_boundry, VHList v_boundry, Arrangement_2 &arr, int d) {

    if (points.size() <= 2) {
        std::cout << "==>> nothing to do with " << points.size() << " points." << " so we return..." << std::endl;
        return;
    }

    std::cout << "==>> current polygon is:" << std::endl;
    write(ch_boundry);

    PointList candidates;

    // decide whether we must partition or prune the given polygon
    bool partition = decide(v_boundry, candidates);

    // perform the partition operation when all degrees are atmost 3, otherwise there is
    //some point of degree 4 or 5, so we isolate it by pruning. this prevent other vertices to connect
    //to this vertex.

    if (partition || !enablePrune) {

        std::cout << "==>> partitioning... " << std::endl;
        PointList left, right;
        Point middle;

        if (candidates.size() == 5) { // get middle one of 5 vertices of degree 3
            std::sort(candidates.begin(), candidates.end());
            middle = candidates[candidates.size() / 2];
            std::cout << "set middle1 of " << candidates.size() << " candidates," << " middle=" << middle << " depth=" << d << std::endl;

        } else { // in this case the middle could be any vertex not x extreme, anyway I prefer the middle one.
            middle = getMiddle(ch_boundry);
            std::cout << "middle2 of " << ch_boundry.size() << " points on the CH. middle=" << middle << ", depth=" << d << std::endl;
        }

        //start partitioning the polygon into two sub polygons
        splitPoints(points, middle, left, right);
        std::cout << "left=" << left.size() << " right=" << right.size() << std::endl;

        // compute convex hull of left and right pointsA
        VHList v_boundry_left, v_boundry_right;
        PointList boundry_left, boundry_right;
        std::cout << "create convex hull of " << left.size() << " points on left " << "depth=" << d << std::endl;
        CGAL::convex_hull_2(left.begin(), left.end(), back_inserter(boundry_left));

        std::cout << "create convex hull of " << right.size() << " points on right " << "depth=" << d << std::endl;
        CGAL::convex_hull_2(right.begin(), right.end(), back_inserter(boundry_right));

        addToDCEL(arr, boundry_left, v_boundry_left);
        addToDCEL(arr, boundry_right, v_boundry_right);

        // recurse for left and right subpolygons
        std::cout << "==>> do left points " << " depth=" << d + 1 << std::endl;
        ST(left, boundry_left, v_boundry_left, arr, d + 1);

        std::cout << "==>> do right points" << " depth=" << d + 1 << std::endl;
        ST(right, boundry_right, v_boundry_right, arr, d + 1);

    } else {

        // perform pruning, there is at least one point with degree greater than 3
        std::cout << "==>> pruning... \n";

        //choose vertex with max degree on the polygon for pruning
        int n = v_boundry.size();
        int max_degree = 0, max_i = 0;
        for (int i = 0; i < n; i++) {

            if (v_boundry[i]->degree() > max_degree) {
                max_degree = v_boundry[i]->degree();
                max_i = i;
            }
        }

        std::cout << "max degree = " << max_degree << " point=" << v_boundry[max_i]->point() << std::endl;

        int i = 0;
        for (i = 0; i < points.size(); i++) {
            if (points[i] == v_boundry[max_i]->point()) break;
        }
        PointList::iterator p_itr = points.begin();
        std::advance(p_itr, i);
        std::cout << "removing point " << *p_itr << std::endl;
        points.erase(p_itr);

        // construct the convex hull of remaining points
        PointList boundry;
        VHList v_boundry1;
        std::cout << "convex hull of " << points.size() << " points of remainders " << "depth=" << d << std::endl;
        CGAL::convex_hull_2(points.begin(), points.end(), back_inserter(boundry));
        addToDCEL(arr, boundry, v_boundry1);

        std::cout << "==>> do remaining points " << " depth=" << d + 1 << std::endl;

        // recurs for the remaining points and it's subpolygon
        ST(points, boundry, v_boundry1, arr, d + 1);
    }//else
}

void draw(PointList points, QGraphicsScene* scene) {


    int n = points.size();
    for (int i = 0; i < n; i++) { // construct boundary of CH in CCW order

        Point p1 = points[i];
        Point p2 = points[(i + 1) % n];

        scene->addEllipse((double)p1.x(), (double)p1.y(), 0.08, 0.08);
        scene->addEllipse((double)p2.x(), (double)p2.y(), 0.08, 0.08);

        scene->addLine((double)p1.x(),(double) p1.y(), (double)p2.x(),(double) p2.y(), QPen(Qt::blue));

    }
}

void draw(Arrangement_2 arr, QGraphicsScene* scene) {

    Arrangement_2::Halfedge_const_iterator hi = arr.halfedges_begin();

    for (hi = arr.halfedges_begin(); hi != arr.halfedges_end(); hi++) {

        Point p1 = hi->source()->point();
        Point p2 = hi->target()->point();

        scene->addLine((double)p1.x(),(double) p1.y(), (double)p2.x(),(double) p2.y(), QPen(Qt::blue));

        QGraphicsEllipseItem* gi = scene->addEllipse((double)p1.x() - 1.5, (double)p1.y() - 1.5, 3, 3);
        QString qst;
        qst.append("(").append(QString::number((int) p1.x(), 10)).append(',').append(QString::number((int) p1.y(), 10)).append(")");
        gi->setToolTip(qst);

        if (hi->source()->degree() > 5) {
            gi = scene->addEllipse((double)p1.x() - 2, (double)p1.y() - 2, 4, 4);
            gi->setBrush(QBrush(Qt::red, Qt::SolidPattern));
        } else
            gi->setBrush(QBrush(Qt::gray, Qt::SolidPattern));

        gi->setPen(QPen(Qt::black));

    }

}

void initST(QGraphicsScene * scene) {

    PointList v;
    std::cout << "Reading points ..." << std::endl;
    std::ifstream in("input.txt");
    std::istream_iterator<Point> begin(in), end;
    std::copy(begin, end, std::back_inserter(v));
    //    std::random_shuffle(v.begin(), v.end());
    //        CGAL::spatial_sort(v.begin(), v.end());
    write(v);

    Arrangement_2 arr;
    VHList v_boundry;
    PointList boundry;
    std::cout << "convex hull of " << v.size() << " points " << "depth=" << 0 << std::endl;
    CGAL::convex_hull_2(v.begin(), v.end(), back_inserter(boundry));
    addToDCEL(arr, boundry, v_boundry);
    ST(v, boundry, v_boundry, arr, 0);

    draw(arr, scene);
    //    draw(v, scene);
}

int main(int argc, char **argv) {

    if (argc > 1) {
        enablePrune = false;
        std::cout << std::endl << ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> Pruning is disabled---------------" << std::endl;
    } else {
        std::cout << "input an argument to the program to disable pruning......." << std::endl;
    }

    QApplication app(argc, argv);
    QGraphicsScene scene;
    //    scene.setSceneRect(1, -1, 1, 1);

    QGraphicsView* view = new QGraphicsView(&scene);
    CGAL::Qt::GraphicsViewNavigation navigation;
    view->installEventFilter(&navigation);
    view->viewport()->installEventFilter(&navigation);

    view->setRenderHints(QPainter::Antialiasing);

    QGraphicsTextItem * io = new QGraphicsTextItem;
    QFont font;
    font.setPixelSize(5);
    font.setBold(false);
    font.setFamily("tahoma");


    io->setPos(-100, -90);
    io->setFont(font);
    scene.addItem(io);
    if (enablePrune) {
        io->setPlainText("Pruning is enabled");
        io->setToolTip(QString("run with an argument to disable pruning"));
    } else
        io->setPlainText("Pruning is disabled, red vertices are of >5 degree ");

    initST(&scene);

    view->setMinimumSize(600, 600);
    view->scale(3, 3);
    view->show();
    return app.exec();
}
